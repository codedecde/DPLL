Control.Print.printDepth := 100;
datatype Term = V of string | F of string * (Term list)
datatype Form = PRED of string * (Term list) | NOT of Form | AND of Form * Form | OR  of Form * Form | FORALL of string * Form | EXISTS of string * Form

(* Part I *)
(* Assumption : The alphabet for Term and Pred are different*)

local 
	fun length ([]) = 0
		|length (x::xs) = 1 + length(xs)
	fun searchHelper([])(_) = true
		|searchHelper((x,l_x)::xs)((y,l_y)) = if x=y then l_x = l_y else searchHelper(xs)((y,l_y))
	fun removeDuplicates(nil) = nil
		|removeDuplicates(x::xs) = x:: removeDuplicates( List.filter (fn y => y <> x) (xs));
	fun search(NONE)(t) = NONE
		|search(SOME(xs))(t) = if searchHelper(xs)(t) then SOME(removeDuplicates(t::xs)) else NONE
	fun searchTermList(NONE)(_) = NONE
		|searchTermList(SOME(xs))([]) = SOME(xs)
		|searchTermList(SOME(xs))(y::ys) = searchTermList(searchTerm(SOME(xs))(y))(ys)
	and
		searchTerm(NONE)(_) = NONE
		|searchTerm(SOME(xs))(V(x)) = search(SOME(xs))((x,0))
		|searchTerm(SOME(xs))(F(a,b)) = searchTermList(search(SOME(xs))((a,length(b))))(b)

in
	fun isValidForm (_, NONE) = NONE
		|isValidForm (NOT(x), z) = isValidForm(x,z)
		|isValidForm (AND(x,y), z) = isValidForm(y, isValidForm(x,z))
		|isValidForm (OR (x,y) , z) = isValidForm(y, isValidForm(x,z)) 
		|isValidForm (FORALL(x,y), z) = isValidForm(y,z)
		|isValidForm (EXISTS(x,y) ,z ) = isValidForm(y,z)
		|isValidForm (PRED(x,y), z) = searchTermList( search (z) (x, length(y)) )(y)
end

(* Part II *)

