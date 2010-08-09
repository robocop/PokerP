type card_type = 
  | Ace
  | King
  | Queen
  | Jack
  | V of int

type color = 
    Hearts
  | Spades
  | Clubs
  | Diamonds

type card = card_type * color;;

type hand = 
  | Royal_flush
  | Straight_flush of card
  | Four_of_a_kind of card * card list
  | Full of card * card
  | Flush of card
  | Straight of card
  | Three_of_a_kind of card * card list
  | Two_pair of card * card * card list
  | Pair of card * card list
  | High_card of card list

exception Invalid_List;;

let ($) f a = f a;;
let id a = a;;

(* take_drop splits a list in two on the n-th element *)
let take_drop n l = 
  let rec take' acc n = function
    | [] -> (List.rev acc, [])
    | e::l ->
	if n <= 1 then (List.rev $ e::acc, l)
	else take' (e::acc) (n-1) l
  in take' [] n l
;;

let eval_type = function
  | Ace -> 14
  | King -> 13
  | Queen -> 12
  | Jack -> 11
  | V e -> e
let eval_card (t,_) = eval_type t


module Heap = 
struct
  let l_cardt = [Ace; King; Queen; Jack; V 10; V 9; V 8; V 7; V 6; V 5; V 4; V 3; V 2]
  let l_colors = [Hearts; Spades; Clubs; Diamonds]
  let init() = Random.self_init()
  (* retourne true avec une probabilite de 1/n *)
  let prob n () = Random.int n = 0
  let rec make_tl e = function
    | [] -> []
    | h::t -> (h, e)::make_tl e t
  (* Retourne le jeu de 52 cartes *)
  let init_cards = List.concat $ List.map (fun e -> make_tl e l_cardt) l_colors;;

  type heap = int * card list
  let init_heap = (52, init_cards)

  let take_card (n, cards) = 
    let rec aux l c = function
      | [] -> failwith "empty heap"
      | e::tail ->
	  if prob c () then (e, (n-1, l@tail))
	  else
	    aux (e::l) (c-1) tail
    in
      aux [] n cards
  let select_card card (n, list) = 
    let rec aux l = function
      | [] -> failwith "card not found"
      | e::t ->
	  if e = card then (n-1, l@t)
	  else
	    aux (e::l) t
    in
      aux [] list

  let rec fusion = function
    | ([], li) | (li, []) -> li
    | ca::queue_a, cb::queue_b ->
	let bonne_tete, queue, autre_demi_liste =
	  if eval_card ca > eval_card cb
	  then ca, queue_a, cb::queue_b
	  else cb, queue_b, ca::queue_a in
	  bonne_tete :: fusion (queue, autre_demi_liste)
  let rec insert elem list = match list with
    |  [] -> elem::[]
    |  tete::queue ->
	 if eval_card elem > eval_card tete then elem :: list
	 else tete :: insert elem queue
end;;

module Eval = 
struct
  let same f l = 
    let rec same' v = function
      | [] -> true
      | c::l ->
	  if c <> v then false
	  else same' v l
    in
    let l = List.map f l in
      same' (List.hd l) (List.tl l)
  (* Makes sure the elements of the list are consecutive *)
  let consecutive l = 
    let rec consecutive' c = function
      | [] -> true
      | a::l ->
	  if a <> c-1 then false
	  else 
	    consecutive' a l
    in
    let nl = List.map eval_card l in
      consecutive' (List.hd nl) (List.tl nl)
  (* Using a sorted list, find_partition looks for a subset l of length n of the list where (f l) is verified.
     Returns (subset_l, rest_of_list) *)
  let find_partition f n l = 
    let rec find_partition' ll f n = function
      | [] -> ([], List.rev ll)
      | e::list ->
	  let l,l' = take_drop n (e::list) in
	    if List.length l = n then
	      if f l then (l, (List.rev $ ll)@l')
	      else find_partition' (e::ll) f n list
	    else
	      ([], (List.rev ll)@e::list)
    in find_partition' [] f n l
  let full l = match find_partition (same fst) 3 l with
    | ([], _) -> ([], [], [])
    | (l, l') ->
	match find_partition (same fst) 2 l' with
	  | ([], _) -> ([], [], [])
	  | (pair, l'') ->
	      (l, pair, l'')
  let two_pair l =  match find_partition (same fst) 2 l with
    | ([], _) -> ([], [], [])
    | (p1, l) ->
	match find_partition (same fst) 2 l with
	  | ([], _) -> ([], [], [])
	  | (p2, l') ->
	      (p1, p2, l')

  (* Looks for the poker hands in a list of 7 cards, ie transforms a list of 7 cards into a poker hand *)
  let eval_list main = 
      match main with
	  (* Royal flush *)
	| [(Ace,c0); (King,c1); (Queen,c2); (Jack,c3); (V 10, c4); _; _] when same id [c0;c1;c2;c3;c4] ->
	    Royal_flush
	  (* Straight flush *)
	| [a;b;c;d;e;f;_] when consecutive [a;b;c;d;e] && same snd [a;b;c;d;e] -> 
	    Straight_flush(f)
	| l when List.length l = 7 ->
	    (* Four of a kind *)
	    begin match find_partition (same fst) 4 main with
	      | (a::l, l') ->
		  Four_of_a_kind(a, l')
	      | ([], _) -> 
		  (* Full *)
		  begin match full main with
		    | (a::l, b::l', _) ->
			Full(a, b)
		    | (_, _, _) ->
			(* Flush *)
			begin match find_partition (same snd) 5 main with 
			  | (a::l, _) ->
			      Flush a
			  | _ -> 
			      (* Straight*)
			      begin match find_partition consecutive 5 main with 
				| (a::l, _) ->
				    Straight a
				| _ -> 
				    (*  Three_of_a_kind *)
				    begin match find_partition (same fst) 3 main with 
				      | (a::_, l) ->
					  Three_of_a_kind(a, l)
				      | _ -> 
					  (* Two pairs *)
					  begin match two_pair main with 
					    | (a::_, b::_, l) ->
						Two_pair(a, b, l)
					    | _ -> 
						(* Pair *)
						begin match find_partition (same fst) 2 main with 
						  | (a::_, l) ->
						      Pair(a, l)
						  | _ ->
						      (* High card *)
						      High_card main
						end
					  end
				    end
			      end
			end
		  end
	    end
	| _ -> raise Invalid_List
	    
(* Compares two poker hands *)
  let compare_hand a b = 
    let compare_hand' = function
      | Royal_flush -> 9
      | Straight_flush _ -> 8
      | Four_of_a_kind(_,_) -> 7 
      | Full(_,_) -> 6 
      | Flush _ -> 5
      | Straight _ -> 4
      | Three_of_a_kind(_,_) -> 3
      | Two_pair (_,_,_) -> 2 
      | Pair (_,_) -> 1
      | High_card _ -> 0
    in

    let rec compare_list = function
      | [], [] -> 0
      | e::l, [] -> 1
      | [], e::l -> -1
      | a::l, b::l' ->
	  if eval_card a > eval_card b then 1
	  else if eval_card a < eval_card b then -1
	  else 
	    compare_list (l, l')
    in
    let compare_kickers = function
      | Straight_flush a, Straight_flush b 
      | Flush a, Flush b
      | Straight a, Straight b -> 
	  compare_list ([a], [b])
      | Four_of_a_kind(a,la),  Four_of_a_kind(b, lb) 
      | Three_of_a_kind(a, la), Three_of_a_kind(b, lb) 
      | Pair(a, la), Pair (b, lb) ->
	  compare_list (a::la, b::lb)
      | Full(ba, pa), Full(bb, pb) -> compare_list ([ba;pa], [bb; pb])
      | Two_pair(a1,a2, la), Two_pair(b1,b2, lb) -> compare_list (a1::a2::la, b1::b2::lb)
      | High_card la, High_card lb -> compare_list (la, lb)
      | (_, _) -> 0
    in
    let a', b' = compare_hand' a, compare_hand' b in
      if a' > b' then 1
      else if a' < b' then -1
      else
	compare_kickers (a, b)
  (* Compare 2 hand of 7 cards, cards have to be sort. *)
  let compare_list a b = 
     compare_hand (eval_list a) (eval_list b) >= 0
end;;

type tour_type = 
    Preflop
  | Flop
  | Turn
  | River
  | End

(* représente l'état d'un jeu *) 
type game = 
{
  (* le tas de cartes restantes *)
  heap: Heap.heap;
  (* Ou on en est dans la distribution des cartes *)
  tour: tour_type;
  (* nombres de joueurs sur la table *)
  num_players:int;
  (* notre postion sur la table *)
  my_pos: int;
  my_cards:card list;
  table: card list;
  (* cartes des adversaires, dans un array, si il y a 8 joueurs dans la table, l'array fait donc 7 élements (nos propres cartes sont stockées dans my_cards) *)
  players_cards: card list array
  
}

let init c0 c1 my_pos n_players = 
  {
    heap = Heap.select_card c1 (Heap.select_card c0 Heap.init_heap);
    tour = Preflop;
    num_players = n_players;
    my_pos = my_pos;
    my_cards = Heap.insert c1 [c0];
    table = [];
    players_cards = Array.make (n_players-1) []
  }
;;
let next state = 
  let next' state = match List.length $ state.table with
    | 0 -> Flop
    | 3 -> Turn
    | 4 -> River
    | 5 -> End
    | _ -> failwith "invalid state"
  in
    {state with tour = next' state }
;;
(* distribue 2 cartes aléatoirement a chaqu'un des joueurs et passe de l'état pre_flop à flop*)
let foward_preflop state= 
  let heap = ref state.heap in
    for i = 0 to state.num_players -2 do
      let c0, h0 = Heap.take_card !heap in
      let c1, h1 = Heap.take_card h0 in
	state.players_cards.(i) <- Heap.insert c1 [c0];
	heap := h1
    done;
    {state with heap = !heap; tour = Flop}
;;
let foward state = match state.tour with
  | Preflop -> 
      next $ foward_preflop state
  | Flop -> 
      let c1, h1 =  Heap.take_card state.heap in
      let c2, h2 =  Heap.take_card h1 in
      let c3, h3 =  Heap.take_card h2 in
	next {state with heap = h3; table = Heap.insert c3 (Heap.insert c2 [c1]); tour = Turn}
  | Turn -> 
      let c, h =  Heap.take_card state.heap in
	next {state with heap = h; table = Heap.insert c state.table; tour = River}
  | River -> 
      let c, h =  Heap.take_card state.heap in
	next {state with heap = h; table = Heap.insert c state.table; tour = End}
  | End -> state
;;
let h = init (V 10, Clubs) (V 9, Clubs) 2 8;;

let h = foward h;;

(* determine d'un etat si on est gagnant*)
let are_you_win game = 
  let rec compare mines = function
    | [] -> true
    | j::l ->
	let player = Heap.fusion (game.table, j) in
	  if Eval.compare_list player mines then false
	  else compare mines l
  in
    compare $ Heap.fusion (game.my_cards ,game.table) $ (Array.to_list game.players_cards)
	    
;;

let make f n = 
  let rec aux l = function
    | 0 -> l 
    | n -> aux $ f ()::l $ n-1
  in
    aux [] n
;;
let compute_prob s t= 
 let a, b, c = match t with
    | Preflop -> (80,15,5)
    | Flop -> (80, 0, 19)
    | Turn -> (300,0,60)
    | River -> (10000,0,0)
    | End -> (0,0,0)
 in
  (* Printf.printf "(%d, %d, %d)" a b c; *)
  let rec compute_prob' state = 
    let count n = 
      let l = make (fun () -> compute_prob' $ foward state) n in
	List.fold_left (fun (x0, y0) (x1,y1) -> (x0+x1, y0+y1)) (0,0) l 
    in
      match state.tour with
	| End ->
	    ((if are_you_win state then 1 else 0), 1)
	| River -> count c
	| Turn ->  count c
	| Flop ->  count b
	| Preflop -> count a
  in
    compute_prob' s
;;

let get_prob s t = let a, n = compute_prob s t in float_of_int a /. float_of_int n;;


let rec scan_card () = 
  let scan_color s= 
    print_endline s;
    match s with
      | "h" -> Hearts
      | "s" -> Spades
      | "c" -> Clubs
      | "d" -> Diamonds
      | _ -> failwith "invalid color: color is in {h,s,c,d}"
  in
  let scan_type_card s =
    print_endline s; 
    match s with
      | "a" -> Ace
      | "k" -> King
      | "q" -> Queen
      | "j" -> Jack
      | card when card.[0] = 'v' -> 
	  V (int_of_string (String.sub card 1 (String.length card -1)))
      | _ -> failwith "invalid type card, card is in {a, k, q, j, v int)"
  in
  let scan () =
    let s0 = read_line() in
    let s1 = read_line() in
      (scan_type_card s0, scan_color s1)
  in
    try
      scan () 
    with 
      | Failure s -> 
	  print_endline s;
	  scan_card ()
;;

let add_on_table c state=
   {state with heap = Heap.select_card c state.heap; table = Heap.insert c state.table}
;;
let _ = 
  Random.self_init();
  print_endline "preflop";
  let nb = read_int (print_endline "nombre de joueurs sur la table ?") in
  print_endline "entrez vos deux cartes";
  let c0 = scan_card () in
    print_endline "card 1 ok";
  let c1 = scan_card () in
    print_endline "card 2 ok";
  let h = init c0 c1 2 nb in
    Printf.printf "probabilite de gain estime : %f \n" (get_prob h Preflop);
    print_endline "entrez les 3 cartes du flop";
    let c0, c1, c2 = scan_card (), scan_card (), scan_card () in
    let h = add_on_table c2 (add_on_table c1 (add_on_table c0 h)) in
      Printf.printf "probabilite de gain estime : %f \n" (get_prob h Flop);
      print_endline "entrez la carte du turn";
      let h = add_on_table (scan_card()) h in
	Printf.printf "probabilite de gain estime : %f \n" (get_prob h Turn);
	print_endline "entrez la carte du river";
	 let h = add_on_table (scan_card()) h in
	   	Printf.printf "probabilite de gain estime : %f \n" (get_prob h River)


  
