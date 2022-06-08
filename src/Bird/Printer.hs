module Bird.Printer where

import Data.List (intersperse)
import Data.Monoid

type Layout = String

pretty  :: Int -> Doc -> Layout
        -- `pretty n d` should produce the "best" layout of d, with width under
        -- `n` characters.
layouts :: Doc -> [Layout]
        -- `layouts d` produces *all* the layouts of `d`.
text    :: String -> Doc
        -- `text s` is a primitive layout, just containing the string `s`
newline :: Doc
        -- `newline` is a layout that introduces a line break.
nest    :: Int -> Doc -> Doc
        -- `nest i` introduces a hanging indent of `i` spaces.  (That is, it
        -- applies on all lines *after* the first)
group   :: Doc -> Doc
        -- `group d` denotes that `d` *could* be laid out on a single line.


{-

A term-based implementation
===========================

We'll start by representing documents exactly following the intended operations,
with one constructor for each operation.

-}

data Doc = Empty
         | Newline
         | Text String
         | Nest Int Doc
         | Group Doc
         | Doc :<>: Doc
  deriving (Show) -- although that's not how we want to view these...

text    = Text
newline = Newline
nest    = Nest
group   = Group

instance Semigroup Doc
    where (<>) = (:<>:)

instance Monoid Doc
    where mempty = Empty


{-

Strictly speaking, this implementation doesn't follow the laws.  For example,
equation (2) says that empty <> empty = empty, but here we get `Empty :<>:
Empty` on the left-hand side, and just Empty on the right.  We have to be
slightly subtler in our understanding of the laws: we're not interested in the
*internal* representation of `Doc` such as the *observable* consequences.  What
is observable about a `Doc`?  Perhaps the best answer is the layouts it
generates.  What we really want from the laws is that, for example, `empty <>
empty` generates all the same layouts as `empty`, and that holds for this
implementation as well.

-}

{-

We can now define flatten following its equations

-}

flatten :: Doc -> Doc
flatten Empty      = Empty
flatten Newline    = Text " "
flatten (Text s)   = Text s
flatten (d :<>: e) = flatten d :<>: flatten e
flatten (Nest i d) = flatten d
flatten (Group d)  = flatten d

{-

Our goal is to push choice down, not pull choice up.  To make this easier, we're
going to work on a slightly different intermediate representation: pairs of
indentations and documents.  The laws for `nest` (from 5A) let us pull nests out
to the front and combine them; we're essentially capturing those laws in data
form.

-}

type IDoc = (Int, Doc)


{-

Now we can write a layouts function that uses "indented documents".

-}

layouts d = layr [(0, d)]
    where layr :: [IDoc] -> [Layout]
          layr [] = [""]
          layr ((i, d :<>: e) : ids) = layr ((i, d) : (i, e) : ids)
          layr ((_, Empty) : ids) = layr ids
          layr ((i, Newline) : ids) = ['\n' : replicate i ' ' ++ s | s <- layr ids]
          layr ((_, Text s) : ids) = [s ++ t | t <- layr ids]
          layr ((i, Nest j d) : ids) = layr ((i + j, d) : ids)
          layr ((i, Group d) : ids) = layr ((i, flatten d) : ids) ++ layr ((i, d) : ids)

{-

The real value comes in writing our `pretty` function, however.  First, because
we can write flatten as an operator on `Doc`s, we're no longer doing terrible
text manipulation.  Second, because we're pushing choice down, we can generate
just enough of each possibility to reject it.

-}

pretty w d = best w [(0, d)]
    where best :: Int -> [IDoc] -> Layout
          best _ [] = ""
          best r ((i, d :<>: e) : ids) = best r ((i, d) : (i, e) : ids)
          best r ((_, Empty) : ids) = best r ids
          best _ ((i, Newline) : ids) = '\n' : replicate i ' ' ++ best (w - i) ids
          best r ((i, Text s) : ids) = s ++ best (r - length s) ids
          best r ((i, Nest j d) : ids) = best r ((i + j, d) : ids)
          best r ((i, Group d) : ids) = better r (best r ((i, flatten d) : ids)) (best r ((i, d) : ids))

          better :: Int -> Layout -> Layout -> Layout
          better w s t | length s' <= w = s
                       | otherwise      = t
              where s' = takeWhile ('\n' /=) s

{-

Some useful routines

-}

cat :: [Doc] -> Doc
cat = mconcat
