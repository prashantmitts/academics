open List;;

(*User Defined types*)
(*Naturals 0,1,2,3,4,5,6..... as O,S(0),S(S(0)),S(S(S(0))),S(S(S(S(0)))),S(S(S(S(S(0))))),S(S(S(S(S(S(O))))))....*)
type nat = O | S of nat;;
(*The sign of Big Integer Type*)
type sign = Pos | Neg;;
(*The sequence of integers which represent value eg in decimal [1;2;3;5;2;4] or in binary [1;0;1;0;1;1]*)
(*The sequnce follows the least to most significant digit*)
type digitseq = int list;;
(*Big Integer Type which is triple of sign , base and digit sequnce*)
type bigint = sign*int*digitseq;;

(*1*)
(*Gives the max integer permisible by the interpreter*)
(*val maxint : unit -> int = <fun>*)
let maxint () = 
	let rec max_int n = 
		if ((2*n) <= 0) then
			if ((n+1) < 0) then
				n
			else max_int(n+1)
		else
			max_int(2*n) in
	max_int(1);;

(*2*)
(*Checks weather the given Big Integer with bigint type follow the rules*)
let check_bigint (big : bigint) =
	let check_base n = n > 0 in
	let rec check_seq n l= match l with 
		[] -> true | 
		[x] -> (x > 0 && x < n) | 
		x::xs -> (x >= 0 && x < n) && (check_seq n xs) in
	let rec check_sign (s : sign) n l = 
		if (check_seq n l) then
			if (l == []) then
				s == Pos
			else
				true
		else
			false in
	match big with s,n,l -> (check_base n) && (check_sign s n l) ;;

(*3*)
(*Converts the function from the integer to the big integer with given base*)
let rec int2bigint (n,base) : bigint = 
	let rec convert n r = 
		match n with 
			0 -> [] |
			n -> (n mod r)::(convert (n/r) r) in

	if (base <= 1) then
		if ( base <= 0) then
			raise (Failure "InvalidBase")
		else
			raise (Failure "Base can't be 1")
	else
		if (n >= 0) then
			(Pos,base,(convert n base))
		else
			(Neg,base,convert (-1*n) base);;
		
(*4*)
(*Converts Big Integers to Integer*)
let rec bigint2int (big : bigint) = 
	let rec convert base acc l= 
		match l with 
			[] -> 0 |
			x::xs ->  x*acc + (convert base (acc*base) xs) in

	if check_bigint (big) then
		match big with s,n,l ->
			match s with 
				Pos -> (convert n 1 l) |
				Neg -> -1*(convert n 1 l)
	else
		raise (Failure ("Invalid Big Integer"));;

(*5*)
(*Converts nat to bigints and bigints to nat*)
let rec nat2bigint (natural,base) = 
	let rec nat2int s = 
		match s with 
			O -> 0 |
			S(n) -> 1 + nat2int(n) in
	let integer = nat2int(natural) in
	int2bigint(integer,base);;

let rec bigint2nat (big : bigint) = 
	let rec int2nat n = 
		match n with 
			0 -> O |
			n -> S(int2nat(n-1)) in
	match big with 
		s,n,l -> 
			if (s = Neg) then 
				raise (Failure "Invalid bigint for conversion to natural number")
			else
				int2nat(bigint2int(big));;

(*6*)
(*Adding two bigint's*)
let rec bigplus (big1,big2) = 
	let rec reverse l  = 
		match l with
			[] -> [] |
			x::xs -> (reverse xs)@[x] in

	let rec zero n = if (n = 0) then [] else 0::zero(n-1) in

	let normalize l n = 
		let m = length l in
		(zero (n-m))@l in

	let rec sub l = match l with 
		[] -> [] |
		x::xs -> (-1*x)::sub xs in

	let rec compare l1 l2 = 
		match l1,l2 with
			l1,[] -> true |
			[],y::ys -> false |
			x::xs,y::ys -> 
				if (x > y) then 
					true 
				else
					if (y > x) then 
						false
					else
						compare xs ys in

	let mod2 x y c n =
		let n1 = (x + y + c) mod n in
		let n2 = (x + y + c)/n in
		if (n1 < 0) then
			let n1 = n1 + n in
			let n2 = n2 - 1 in
			(n1,n2)
		else
			(n1,n2) in

	let rec add l1 l2 n c = 
		match l1,l2 with 
			[],[] -> if (c != 0) then [c] else [] |
			x::xs,[] -> (add l1 [c] n 0) |
			[],x::xs -> (add l2 [c] n 0) |
			x::xs,y::ys -> 
				let m1,c = mod2 x y c n in
				m1::(add xs ys n c) in

	let trail_zero l = 
		let rec rem l = 
		match l with
			[] -> [] |
			0::xs -> rem xs |
			x::xs -> l in
		reverse (rem (reverse l)) in

	if (check_bigint(big1) && check_bigint(big2)) then
		match big1,big2 with (s1,base1,l1),(s2,base2,l2) ->
			if (base1 != base2) then
				raise(Failure "Invalid bases are not same")
			else
				if (s1 = s2) then 
					(s1,base1,(add l1 l2 base1 0))
				else
					let n = max (length l1) (length l2) in 
					let l11 = normalize (reverse l1) n in 
					let l22 = normalize (reverse l2) n in
					if compare l11 l22 then 
						(s1,base1,trail_zero((add l1 (sub l2) base1 0)))
					else
						(s2,base1,trail_zero((add l2 (sub l1) base1 0)))
	else
		raise(Failure("Invalid bigint"));;


(*7*)
(*Multiplying 2 bigint's*)
let rec bigtimes (big1,big2) : bigint =

	let mod2 x y c n =
		let n1 = (x + y + c) mod n in
		let n2 = (x + y + c)/n in
		if (n1 < 0) then
			let n1 = n1 + n in
			let n2 = n2 - 1 in
			(n1,n2)
		else
			(n1,n2) in

	let rec add l1 l2 n c = 
		match l1,l2 with 
			[],[] -> if (c != 0) then [c] else [] |
			x::xs,[] -> (add l1 [c] n 0) |
			[],x::xs -> (add l2 [c] n 0) |
			x::xs,y::ys -> 
				let m1,c = mod2 x y c n in
				m1::(add xs ys n c) in

	let trail_zero l = 
		let rec rem l = 
		match l with
			[] -> [] |
			0::xs -> rem xs |
			x::xs -> l in
		reverse (rem (reverse l)) in

	let rec mult l n c n1 = 
		let rec multi l n c n1 = match l with 
			[] -> if (c == 0) then [] else [c] |
			x::xs -> 
				let x1 = (x*n + c) mod n1 in
				let c = (x*n + c)/n1 in
			(x1)::(multi xs n c n1) in
		trail_zero (multi l n c n1) in

	let rec mul l1 l2 n = match l2 with 
		[] -> [] |
		x::xs -> 
			let l11 = mult l1 x 0 n in
			trail_zero (add l11 (0::(mul l1 xs n)) n 0) in

	if (check_bigint(big1) && check_bigint(big2)) then
		match big1,big2 with (s1,base1,l1),(s2,base2,l2) ->
			if (base1 != base2) then
				raise(Failure "Invalid as bases are not same")
			else
				if (s1 = s2) then
					(Pos,base1,(mul l1 l2 base1))
				else
					(Neg,base1,(mul l1 l2 base1)) 
	else
		raise(Failure("Invalid bigint"));;



(*Test the Programs*)
check_bigint (Pos,2,[1;0;1]);;
int2bigint(31,2);;
int2bigint(0,3);;
bigint2int(int2bigint(31,2));;
bigint2int(int2bigint(5,3));;
bigint2nat(int2bigint(0,2));;
