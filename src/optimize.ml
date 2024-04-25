open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> None
  | (var, value) :: t -> if x = var then Some value else lookup t x

let rec optimize env e = match e with
| Int x -> Int x
| Bool x -> Bool x
| ID x -> let v = lookup env x in (match v with Some a -> optimize env a | None -> ID x)
| Binop (op, v1, v2) -> let v1 = optimize env v1 in let v2 = optimize env v2 in (match op with
| Add -> (match (v1, v2) with (Int x, Int y) -> Int (x + y) | Int 0, x | x, Int 0 -> x | _ -> Binop (Add, v1, v2))
| Mult -> (match v1, v2 with (Int x, Int y) -> Int (x * y) | (Int 0, _) | (_, Int 0) -> Int 0 | (Int 1, x) | (x, Int 1) -> x | _ -> Binop (Mult, v1, v2))
| Div -> (match v1, v2 with Int x, Int y -> Int (x/y) | Int 0, _  -> Int 0 | _, Int 0 -> raise DivByZeroError | x, Int 1 -> x | _ -> Binop (Div, v1, v2))
| Sub ->  (match (v1, v2) with (Int x, Int y) -> Int (x - y) | Int 0, x | x, Int 0 -> x |_ -> Binop (Sub, v1, v2))
| Greater -> (match (v1, v2) with (Int x, Int y) -> Bool (x > y) | _ -> Binop (Greater, v1, v2))
| Less -> (match (v1, v2) with (Int x, Int y) -> Bool (x < y) | _ -> Binop (Less, v1, v2))
| GreaterEqual -> (match (v1, v2) with (Int x, Int y) -> Bool (x >= y) | _ -> Binop (GreaterEqual, v1, v2))
| LessEqual -> (match (v1, v2) with (Int x, Int y) -> Bool (x <= y) | _ -> Binop (LessEqual, v1, v2))
| Equal -> if (v1 = v2) then Bool (true) else (match (v1, v2) with | Int a, Int b -> (Bool (a = b))| Bool a, Bool b -> (Bool (a = b)) | _ -> Binop (Equal, v1, v2))
| NotEqual -> if (v1 = v2) then Bool (false) else Binop (NotEqual, v1, v2)
| Or -> (match v1, v2 with Bool x, Bool y -> Bool (x || y) | Bool true, _ | _, Bool true -> Bool true | _ -> Binop (Or, v1, v2))
| And -> (match v1, v2 with Bool x, Bool y -> Bool (x || y) | Bool false, _ | _, Bool false -> Bool true | _ -> Binop (And, v1, v2)))
| Not x -> let x = optimize env x in (match x with Bool t -> Bool (not t) | _ -> Not x)
| If (t, x, y) -> let t = optimize env t in let x = optimize env x in let y = optimize env y in (match t with Bool f -> if f then x else y | _ -> If (t, x, y))
| Let (v,e,r) -> let e = optimize env e in let env = extend env v e in optimize env r
| LetRec (v,t,e,r) -> LetRec(v, t, optimize env e, optimize env r)
| Fun (a,b,c) -> let rec corenv lst = (match lst with (k,v) :: t -> if (k = a) then corenv t else (k,v) :: corenv t | [] -> []) in let env = corenv env in Fun (a, b, optimize env c)
| App (x, y) -> let y = optimize env y in let x = optimize env x in (match x with Fun (a, b, c) -> let env = extend env a y in optimize env c | _ -> App (x, y))
| Record lst -> let rec thrulst ls = match ls with 
      (a,b) :: t -> (a, optimize env b) :: thrulst t
      | [] -> []
      | _ -> lst
in Record (thrulst lst)
| Select (v, e) -> let e = optimize env e in (match e with Record lst -> let rec tlst ls = 
                  match ls with (a,b) :: t -> if (a = v) then optimize env b else  tlst t | _ -> Select (v,e) in tlst lst
                  | _ -> Select (v, e))