(* ch2 *)
(* no gadt *)
module C2 = struct
  (* 2.1 *)
  (* deep encoding *)
  (* type *)
  type tp =
    | Base
    | Arr of tp * tp

  (* term *)
  type tm =
    | Var of x
    | Lam of (x -> tm)
    | App of tm * tm
  and x = vl

  (* shallow encoding *)

  (* atoms are intersection of set of shallow
     values and deep terms *)
  and base = Atom of at
  and vl =
    | VFun of (vl -> vl)
    | VBase of base

  (* normal form *)
  and nf =
    | NLam of (y -> nf)
    | NAt of at
  and at =
    | AApp of at * nf
    | AVar of y
  and y

  (* lambda f x. f x *)
  (* deep embedding *)
  let deep = Lam (fun f -> Lam (fun x -> App (Var f, Var x)))
  (* shallow embedding,
     warning: non exhaustive pattern matching,
     could be solved later by GADT *)
  let shallow = VFun (fun (VFun f) -> VFun (fun x -> f x))

  (* 2.2 *)
  (* NbE normalizes deep term by going through shallow embedding *)

  let rec eval : tm -> vl = function
    | Var x -> x
    | Lam f -> VFun (fun x -> eval (f x))
    | App (m, n) ->
      match eval m with
      | VFun f -> f (eval n)
      | VBase n -> failwith "unidentified functional object"

  (** [reify a v] is the norm form of value [v] and its type [a] *)
  let rec reify : tp -> vl -> nf = fun a v ->
    match a, v with
    | Arr (a, b), VFun f ->
      NLam (fun x -> reify b (f (reflect a (AVar x))))
    | Base, VBase v ->
      let (Atom r) = v in NAt r
    | a, v -> failwith "type mismatch"

  (** [reflect] is the inverse of [reify] *)
  and reflect : tp -> at -> vl = fun a r ->
    match a with
    | Arr (a, b) -> VFun (fun x -> reflect b (AApp (r, reify a x)))
    | Base -> VBase (Atom r)

  let nbe : tp -> tm -> nf = fun a m -> reify a (eval m)

end

(* gadt *)
module C3 = struct

  type _ vl =
    | VFun : ('a vl -> 'b vl) -> ('a -> 'b) vl
    | VBase : base -> base vl

  and 'a x = 'a vl

  and _ tm =
    | Lam : ('a x -> 'b tm) -> ('a -> 'b) tm
    | App : ('a -> 'b) tm * 'a tm -> 'b tm
    | Var : 'a x -> 'a tm

  and _ nf =
    | NLam : ('a y -> 'b nf) -> ('a -> 'b) nf
    | NAt : base at -> base nf
  and _ at =
    | AApp : ('a -> 'b) at * 'a nf -> 'b at
    | AVar : 'a y -> 'a at
  and 'a y (* domain left uninstantiated *)

  and _ tp =
    | Base : base tp
    | Arr : 'a tp * 'b tp -> ('a -> 'b) tp

  and base = Atom of base at (* no (normalizing) closed inhabitant *)

  let rec eval : type a. a tm -> a vl = function
    | Lam f -> VFun (fun x -> eval (f x))
    | Var x -> x
    | App (f, x) ->
      let VFun f = eval f in
      f (eval x)

  let rec reify : type a. a tp -> a vl -> a nf = fun a v ->
    match a, v with
    | Arr (a, b), VFun f ->
      NLam (fun x -> reify b (f (reflect a (AVar x))))
    | Base, VBase v ->
      let Atom r = v in NAt r

  and reflect : type a. a tp -> a at -> a vl = fun a r ->
    match a with
    | Arr (a, b) ->
      VFun (fun x -> reflect b (AApp (r, reify a x)))
    | Base -> VBase (Atom r)

  let nbe : type a. a tp -> a tm -> a nf = fun a m ->
    reify a (eval m)

end

(* partial evaluate printf by typeful normalization *)
module Printf_custom = struct

  type _ vl =
    | VFun : ('a vl -> 'b vl) -> ('a -> 'b) vl
    | VBase : 'a base -> 'a base vl

  and 'a x = 'a vl

  and _ tm =
    | Lam : ('a x -> 'b tm) -> ('a -> 'b) tm
    | App : ('a -> 'b) tm * 'a tm -> 'b tm
    | Var : 'a x -> 'a tm

  and _ nf =
    | NLam : ('a y -> 'b nf) -> ('a -> 'b) nf
    | NAt : 'a base at -> 'a base nf
  and _ at =
    | AApp : ('a -> 'b) at * 'a nf -> 'b at
    | AVar : 'a y -> 'a at
    | APrim : 'a -> 'a base at
    | AConcat : string base at * string base at -> string base at
    | AStringOfInt : int base at -> string base at
  and 'a y (* domain left uninstantiated *)

  and _ tp =
    | Base : 'a base tp
    | Arr : 'a tp * 'b tp -> ('a -> 'b) tp

  and 'a base = Atom of 'a base at (* no (normalizing) closed inhabitant *)

  let rec eval : type a. a tm -> a vl = function
    | Lam f -> VFun (fun x -> eval (f x))
    | Var x -> x
    | App (f, x) ->
      let VFun f = eval f in
      f (eval x)

  let rec reify : type a. a tp -> a vl -> a nf = fun a v ->
    match a, v with
    | Arr (a, b), VFun f ->
      NLam (fun x -> reify b (f (reflect a (AVar x))))
    | Base, VBase v ->
      let Atom r = v in NAt r

  and reflect : type a. a tp -> a at -> a vl = fun a r ->
    match a with
    | Arr (a, b) ->
      VFun (fun x -> reflect b (AApp (r, reify a x)))
    | Base -> VBase (Atom r)

  let nbe : type a. a tp -> a tm -> a nf = fun a m ->
    reify a (eval m)

  type int_ = int base at
  type string_ = string base at
  let string_of_string s = APrim s
  let string_of_int x = AStringOfInt x
  let ( ^ ) s t = AConcat (s, t)

  type (_, _) directive =
    | Lit : string_ -> ('a, 'a) directive
    | String : (string_ -> 'a, 'a) directive
    | Int : (int_ -> 'a, 'a) directive
    | Seq : ('a, 'b) directive * ('b, 'r) directive -> ('a, 'r) directive

  let (^^) a b = Seq (a, b)
  and (!) x = Lit (APrim x)
  and d = Int
  and s = String

  let ex_dir = d ^^ !" * " ^^ s ^^ !" = " ^^ d ^^ !" in " ^^ s

  let rec kprintf : type a b. (a, b) directive -> (string_ -> b) -> a = function
    | Lit s -> fun k -> k s
    | Int -> fun k x -> k (string_of_int x)
    | String -> fun k x -> k x
    | Seq (f, g) -> fun k -> kprintf f (fun v -> kprintf g (
        fun w -> k (v ^ w)))

  let printf dir = kprintf dir (fun id -> id)

  let box f = VFun (fun (VBase (Atom r)) -> f r)

  (* ('a base -> 'b base -> 'c base -> 'd base -> 'e base) tp *)
  let tp = (Arr (Base, Arr (Base, Arr (Base, (Arr (Base, Base))))))

  let tm = box (fun x -> box (fun y -> box (fun z -> box (fun t ->
      reflect Base (printf ex_dir x y z t)))))

  (* (int base -> string base -> int base -> string base -> string base) nf *)
  let pe_print = reify tp tm

  (* TODO: pretty-printing [nf] value *)
end
