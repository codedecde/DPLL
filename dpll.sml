Control.Print.printDepth := 100;
datatype Term = V of string | F of string * (Term list)
datatype Form = PRED of string * (Term list) | NOT of Form | AND of Form * Form | OR  of Form * Form | FORALL of string * Form | EXISTS of string * Form

(* Part I *)
(* Assumption : The alphabet for Term and Pred are different*)

fun removeDuplicates(nil) = nil
	|removeDuplicates(x::xs) = x:: removeDuplicates( List.filter (fn y => y <> x) (xs));

local 
	fun length ([]) = 0
		|length (x::xs) = 1 + length(xs)
	fun searchHelper([])(_) = true
		|searchHelper((x,l_x)::xs)((y,l_y)) = if x=y then l_x = l_y else searchHelper(xs)((y,l_y))	
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
fun subst_term((a,b))(V(x)) = if x = a then b else V(x)
	|subst_term((a,b))(F(x,y)) = F(x,subst_term_list((a,b))(y))
and 
	subst_term_list((a,b))(y) = List.map(fn x=> subst_term((a,b))(x))(y)

fun subst(s)(PRED(x, y)) = PRED(x, subst_term_list(s)(y))
	|subst(s)(NOT(x)) = NOT(subst(s)(x))
	|subst(s)(AND(x,y)) = AND(subst(s)(x), subst(s)(y))
	|subst(s)(OR(x,y)) = OR(subst(s)(x), subst(s)(y))
	|subst((a,b))(FORALL(x,y)) = if a = x then FORALL(x,y) else FORALL(x, subst((a,b))(y))
	|subst((a,b))(EXISTS(x,y)) = if a = x then EXISTS(x,y) else EXISTS(x, subst((a,b))(y))	

fun rename(c)(PRED(x,y)) = PRED(x,y)
	|rename(c)(NOT(x)) = NOT(rename(c)(x))
	|rename(c)(AND(x,y)) = AND(rename(c+1)(x), rename(c+2)(y))
	|rename(c)(OR(x,y)) = OR(rename(c+1)(x), rename(c+2)(y))
	|rename(c)(FORALL(x,y)) = let val t = String.concat(["x", Int.toString(c)]); in FORALL(t , rename(c+1)( subst((x,V(t)))(y) ) ) end
	|rename(c)(EXISTS(x,y)) = let val t = String.concat(["x", Int.toString(c)]); in EXISTS(t , rename(c+1)( subst((x,V(t)))(y) ) ) end

(* Prenix normal Form *)

fun qm(PRED(x,y)) = PRED(x,y)
	|qm(NOT(FORALL(x, y))) = EXISTS(x, qm(NOT(y)))
	|qm(NOT(EXISTS(x, y))) = FORALL(x, qm(NOT(y)))
	|qm(NOT(x)) = NOT(x)
	|qm(AND(FORALL(x,y), w )) = FORALL(x, qm( AND(y, w) ) )
	|qm(AND(EXISTS(x,y), w )) = EXISTS(x, qm( AND(y, w) ) )
	|qm(AND(w, FORALL(x,y) )) = FORALL(x, qm( AND(w, y) ) )
	|qm(AND(w, EXISTS(x,y) )) = EXISTS(x, qm( AND(w, y) ) )
	|qm(AND(x,y)) = AND(x,y)
	|qm(OR(FORALL(x,y), w )) = FORALL(x, qm( OR(y, w) ) )
	|qm(OR(EXISTS(x,y), w )) = EXISTS(x, qm( OR(y, w) ) )
	|qm(OR(w, FORALL(x,y) )) = FORALL(x, qm( OR(w, y) ) )
	|qm(OR(w, EXISTS(x,y) )) = EXISTS(x, qm( OR(w, y) ) )
	|qm(OR(x,y)) = OR(x,y)

fun prenix(PRED(x,y)) = PRED(x,y)
	|prenix(FORALL(x,y)) = FORALL(x, prenix(y))
	|prenix(EXISTS(x,y)) = EXISTS(x, prenix(y))
	|prenix(NOT(x)) = qm( NOT(prenix(x) ) )
	|prenix(AND(x,y)) = qm( AND(prenix(x), prenix(y)))
	|prenix(OR(x,y)) = qm(OR(prenix(x), prenix(y)))

(* Skolemization *)
fun makeFunc(x_list, var_name) = F( String.concat(["f",var_name]) , List.map(fn x=> V(x))(x_list) )

fun skolem(FORALL(x, y))(z) = FORALL(x, skolem(y)(x::z))
	|skolem(EXISTS(x,y))(z) = subst((x, makeFunc(z,x) )) (skolem(y)(z))
	|skolem(x)(z) = x

(* CNF Conversion *)
(* Reference: Slides Page 269 *)
fun nnf(PRED(x)) = PRED(x)
	|nnf(NOT(PRED(x))) = NOT(PRED(x))
	|nnf(NOT(NOT(x))) = x
	|nnf(AND(x,y)) = AND(nnf(x), nnf(y))
	|nnf(NOT(AND(x,y))) = nnf(OR(NOT(x), NOT(y)))
	|nnf(OR(x ,y)) = OR(nnf(x), nnf(y))	
	|nnf(NOT(OR(x,y))) = nnf( AND(NOT(x), NOT(y)))

fun distOR(x, AND(y,z)) = AND(distOR(x,y) , distOR(x,z))
	|distOR(AND(y,z), x) = AND(distOR(y,x) , distOR(z,x))
	|distOR(x,y) = OR(x,y)

fun cnj_of_disj(AND(x,y)) = AND(cnj_of_disj(x), cnj_of_disj(y))
	|cnj_of_disj(OR(x,y)) = distOR(cnj_of_disj(x), cnj_of_disj(y))
	|cnj_of_disj (x) = x

fun cnf(FORALL(x,y)) = FORALL(x,cnf(y))
	|cnf(EXISTS(x,y)) = EXISTS(x,cnf(y))
	|cnf(x) = cnj_of_disj(nnf( x ) )	

(* Part III *)
fun getVariablesFromTL([]) = []
	|getVariablesFromTL(x::xs) = removeDuplicates( getVarsFromTerm(x) @ getVariablesFromTL(xs) )
and 
	getVarsFromTerm(V(x)) = [x]
	|getVarsFromTerm(F(x,y)) = getVariablesFromTL(y)

fun getVariables(PRED(_, term_list)) = getVariablesFromTL(term_list)
	|getVariables(NOT(x)) = getVariables(x)
	|getVariables(OR(x,y)) = removeDuplicates(getVariables(x)@getVariables(y))
	|getVariables(AND(x,y)) = removeDuplicates(getVariables(x)@getVariables(y))
	|getVariables(FORALL(x,y)) = getVariables(y)
	|getVariables(EXISTS(x,y)) = getVariables(y)

fun getSubstSingle(x,0) = []
	|getSubstSingle(x,v) = (x,Int.toString(v))::getSubstSingle(x,v-1)

fun newMap(f)([]) = []
	|newMap(f)(x::xs) = f(x) @ newMap(f)(xs)
fun product(ys,xs) = newMap( fn y => List.map( fn x => y::x )(xs) ) (ys)
fun getSubst(k, []) = [[]]
	|getSubst(k, x::xs) = product(getSubstSingle(x,k), getSubst(k,xs))

fun lookup(a,[]) = ""
	|lookup(a,(b,y)::ys) = if a=b then y else lookup(a,ys)		
fun inst_term_list(subst)([]) = []
	|inst_term_list(subst)(x::xs) = inst_term(subst)(x)::inst_term_list(subst)(xs)
and
	inst_term(subst)(V(a)) = V(lookup(a,subst))
	|inst_term(subst)(F(a,t)) = F(a,inst_term_list(subst)(t))

fun inst_one(subst)(PRED(a, term_list)) = PRED(a, inst_term_list(subst)(term_list))
	|inst_one(subst)(NOT(x)) = NOT(inst_one(subst)(x))
	|inst_one(subst)(OR(x,y)) =  OR(inst_one(subst)(x), inst_one(subst)(y))
	|inst_one(subst)(AND(x,y)) =  AND(inst_one(subst)(x), inst_one(subst)(y))
	|inst_one(subst)(FORALL(x,y)) = inst_one(subst)(y)
	|inst_one(subst)(EXISTS(x,y)) = inst_one(subst)(y)

fun inst([])(form) = []
	|inst(a::ax)(form) = inst_one(a)(form) :: inst(ax)(form)


fun convertOR(PRED(x)) = [PRED(x)]
	|convertOR(NOT(x)) = [NOT(x)]
	|convertOR(OR(x,y)) = convertOR(x) @ convertOR(y)

fun convert2Clause(PRED(x)) = [[PRED(x)]]
	|convert2Clause(NOT(x)) = [[NOT(x)]]
	|convert2Clause(AND(x,y)) = convert2Clause(x) @ convert2Clause(y)
	|convert2Clause(OR(x,y)) = [convertOR(OR(x,y))]
	|convert2Clause(FORALL(x,y)) = convert2Clause(y)
	|convert2Clause(EXISTS(x,y)) = convert2Clause(y)

fun convert2ClauseSet([]) = []
	|convert2ClauseSet(x::xs) = convert2Clause(x) @ convert2ClauseSet(xs)


(* Main DPLL Code *)
fun empty([]) = false
	|empty(x::xs) = if x = nil then true else empty(xs)

fun nc(NOT(NOT(x)) ) = x
	|nc(NOT(x)) = NOT(x)
	|nc(x) = x

local 
	fun findsmallest([])(acc) = acc
		|findsmallest(y::ys)(acc) = if length(y) < length(acc) then findsmallest(ys)(y) else findsmallest(ys)(acc)
	
	fun fphhl(t)([]) = true
		|fphhl(t)(x::xs) = if length( List.filter(fn y => y = nc(NOT(t)) )(x)) <> 0 then false else fphhl(t)(xs)

	fun fphh([])(xs) = NONE
		|fphh(t::ts)(xs) = if fphhl(t)(xs) then SOME(t) else fphh(ts)(xs)

	fun fph(a)(b) = let val v = fphh(a)(b) in if isSome(v) then getOpt(v, List.hd(a)) :: List.filter(fn x=> x<> getOpt(v, List.hd(a)))(a) else [] end

	fun findpure(t)([]) = t
		|findpure(t)(x::xs) = let val v = fph(t)(x::xs) in if v <> nil then v else findpure(x)(xs) end
in 
	fun reorder([]) = []
		|reorder(y::ys) = let 
							val t = findsmallest(ys)(y); 
						  in
						  	if length (t) = 1 then  t :: List.filter(fn x => x <> t)(ys) else 
						  		let
						  			val t2 = findpure(y)(ys)
						  		in 
						  			t2 :: List.filter(fn x => x <> t2)(ys)
						  		end
						  end
end

fun find(x)([]) = false
	|find(x)(y::ys) = if x=y then true else find(x)(ys)

fun setvalue(x)([]) = []
	|setvalue(x)(y::ys) = if find(x)(y) then setvalue(x)(ys) else (List.filter( fn z => z <> nc(NOT(x)) )(y)) :: setvalue(x)(ys)

fun dpll([]) = true
	|dpll(xs) = if empty(xs) then false else dpll_helper(xs)
and 
	dpll_helper(xs) = let
		val y::ys = reorder(xs);
		in
		if dpll( setvalue(List.hd(y))( ys ) ) orelse dpll( setvalue(nc(NOT(List.hd(y))))(List.tl(y) :: ys ) ) then true else false
		end

(* Test cases *)

val p1 = PRED("p",[V("x"), V("y")]);
val p2 = PRED("r",[V("z"), V("y")]);
val p3 = AND(p1,p2);
val p4 = PRED("q",[V("y"), V("z")]);
val p5 = NOT(EXISTS("y", p3));
val p6 = OR(p4, p5);
val p7 = FORALL("x", p6);
val p8 = cnf(skolem(prenix(rename(1)(p7)))([]));
val k = 5;
val v1 = inst(getSubst(k, getVariables(p8) ))(p8);
val v2 = convert2ClauseSet(v1)
val it = dpll(v2)

