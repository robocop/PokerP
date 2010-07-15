type card_type = 
  | Ace
  | King
  | Queen
  | Jack
  | V of int
;;
type color = 
    Hearts
  | Spades
  | Clubs
  | Diamonds
;;
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
;;

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

module Eval = 
struct
  let eval_type = function
    | Ace -> 14
    | King -> 13
    | Queen -> 12
    | Jack -> 11
    | V e -> e
  let eval_card (t,_) = eval_type t

  let sort_list main = 
    let l = List.map (fun c -> (c, eval_card c)) main in
      List.map fst $ List.sort (fun (_,a) (_,b) -> compare b a) l

  (* Useless *)
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
  let eval_list m = 
    let main = sort_list m in
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
end

type tour_type = 
    Preflop
  | Flop
  | Turn
  | River
  | End
;;
(* représente l'état d'un jeu *) 
type game = 
{
  (* Ou on en est dans la distribution des cartes *)
  tour: tour_type;
  (* position du joueur a qui on est en train de distribuer des cartes *)
  num_players:int;
  (* notre postion sur la table *)
  my_pos: int;
  my_cards:card list;
  (* cartes des adversaires, dans un array, si il y a 8 joueurs dans la table, l'array fait donc 7 élements (nos propres cartes sont stockées dans my_cards) *)
  players_cards: card list array
  
}
;;
let init c0 c1 my_pos n_players = 
  {
    tour = Preflop;
    num_players = 0;
    my_pos = my_pos;
    my_cards = [c0;c1];
    players_cards = Array.make n_players []
  }

;;
