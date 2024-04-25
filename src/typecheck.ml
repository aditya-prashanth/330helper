open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound type for " ^ x))
  | (var, value) :: t -> if x = var then value else lookup t x

let rec is_subtype t1 t2 = if t1 = t2 then true else match t1 with 
| TArrow (a, b) -> (match t2 with TArrow (x, y) -> if (is_subtype x a && is_subtype y b) then true else false | _ -> false)
| TRec lst1 -> (match t2 with TRec lst2 -> (depth lst1 lst2) || (width lst1 lst2) || (perms lst1 lst2 && perms lst2 lst1) | _ -> false)
| _ -> false 

and depth l1 l2 = match (l1, l2) with 
| ((a, b) :: x, (c,d) :: y) -> if (is_subtype b d) then true && depth x y else false
|  ([], []) -> true
| _ -> false 

and width l1 l2 = match (l1, l2) with 
| ((a, b) :: x, (c,d) :: y) -> if (b = d) then true && width x y else false
| ([], []) -> true 
| ((a, b) :: x, []) -> true
| _ -> false 

and perms l1 l2 = 
  let rec innerperm x ls = match ls with
  | h :: t -> if (h = x) then true else false || innerperm x t
  | [] -> false
in match l1 with 
| h :: t -> (innerperm h l2) && perms t l2
| [] -> false  


let rec typecheck gamma e = match e with
| Ast.Int a -> TInt
| Ast.Bool a -> TBool
| ID a -> lookup gamma a
| Binop (op, a, b) -> let e1 = typecheck gamma a in let e2 = typecheck gamma b in (match op with
                      | Add | Sub | Mult |Div ->  if (e1, e2) = (TInt, TInt) then TInt else raise (TypeError "invalid add")
                      | Greater | Less | GreaterEqual | LessEqual -> if (e1, e2) = (TInt, TInt) then TBool else raise (TypeError "invalid comparison")
                      | Equal | NotEqual -> if (e1 = e2) then TBool else raise (TypeError "invalid equality")
                      | Or | And -> if (e1, e2) = (TBool, TBool) then TBool else raise (TypeError "invalid boolean")
                      | _ -> raise (TypeError "invalid operator"))
| If (tf, a, b) -> let tf = typecheck gamma tf in if (tf <> TBool) then raise (TypeError "invalid if condition") else 
        let e1 = typecheck gamma a in let e2 = typecheck gamma b in if (e1 = e2) then e1 else raise (TypeError "if outcomes are not of type")
| Fun (x, t, e) -> let gamma = extend gamma x t in TArrow (t, typecheck gamma e)
| App (a,b) -> let e2 = typecheck gamma b in let e1 = typecheck gamma a in 
            (match e1 with TArrow(x,y) when x = e2 -> y | _ -> raise (TypeError "invalid app"))
| Record lst -> let rec thrurec l = (match l with (a, b) :: t -> (a, typecheck gamma b) :: thrurec t | [] -> []) in TRec (thrurec lst)
| Select (x, lst) -> let lst = typecheck gamma lst in (match lst with TRec l -> let rec thru ls = 
                (match ls with (a,b) :: t -> if (a = x) then b else thru t | [] -> raise (TypeError "var not found in record")) in thru l
                | _ -> raise (TypeError "not a record"))
| Not x -> let e = typecheck gamma x in if (e = TBool) then TBool else raise (TypeError "not a bool")
| Let (f, e, t) -> let e = typecheck gamma e in let gamma = extend gamma f e in typecheck gamma t
| LetRec (f, x , e, t) -> let gamma = extend gamma f x in let e = typecheck gamma e in if (x = e) then typecheck gamma t else raise (TypeError "not typed")