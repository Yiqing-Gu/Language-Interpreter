parent(lee, virginia).
parent(lee, bob).
parent(lee, suzy).
parent(virginia, garrett).
parent(bob, robby).
parent(suzy, chris).
parent(suzy, jamie).
parent(lee, bob)?                         
parent(suzy, chris)?                      
parent(suzy, bob)?                        
parent(bob, garrett)?                     
parent(lee, jamie)?                       
generations(lee, virginia, succ(zero)).
generations(lee, garrett, succ(succ(zero))).
generations(lee, robby, succ(succ(zero))).
generations(suzy, jamie, succ(zero)).
generations(lee, virginia, zero)?           
generations(lee, virginia, succ(zero))?     
generations(lee, virginia, succ(succ(zero)))? 
children(lee, cons(virginia, cons(bob, cons(suzy, nil)))).
children(suzy, cons(chris, cons(jamie, nil))).
children(lee, cons(virginia, cons(bob, nil)))?
children(lee, cons(bob, cons(suzy, nil)))?               
children(lee, cons(bob, cons(virginia, cons(suzy, nil))))?
children(suzy, cons(chris, cons(jamie, nil)))?
