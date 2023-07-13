# JILI
JILI is a novel programming language that supports functional programming, type-checking, mutation, arrays, recursion, and more

# Syntax
A JILI program consists of a single expression.

The concrete syntax of the JILI expressions with these additional features can be captured with the following EBNFs.

  expr	 	=	 	num
    |	 	string
 	 	|	 	id
 	 	|	 	{if expr expr expr}
 	 	|	 	{var {[id : ty = expr] ...} in expr}
 	 	|	 	{[id : ty] ... => expr}
 	 	|	 	{rec {id = {[id : ty] ... : ty => expr}} in expr}
 	 	|	 	{expr expr ...}

    
  ty	 	=	 	num
 	 	|	 	bool
 	 	|	 	str
 	 	|	 	{ty ... -> ty}

    
  operator	 	=	 	+
 	 	|	 	-
 	 	|	 	*
 	 	|	 	/
 	 	|	 	num-eq?
 	 	|	 	str-eq?
 	 	|	 	<=
 	 	|	 	substring

    
... where an id is not if, :, =, var, in, rec, =>, or ->

# Try it out

Download Racket from [https://www.racket-lang.org/] and open the .rkt file in the DrRacket IDE [https://docs.racket-lang.org/drracket/]
