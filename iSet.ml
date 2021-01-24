(* ======= Autor: Jakub Korzeniewski ======= *)
(* ============== Arytmetyka =============== *)
(* ====== Code Review: Michał Skwarek ====== *)

(* == Testy: https://gitlab.com/MIMUW-wpf/testy-iset/-/tree/master/tests == *)

(* ========== Operatory ========== *)


(* zastąpienie operacji dodawania
   dodawaniem z zabezpieczeniem przed wyjściem poza zakres *)
let (+) a b =
  if a < 0 && b < 0 && a >= min_int - b then min_int
  else if a >= 0 && b >=0 && a >= max_int - b then max_int
  else a + b;;


(* ========== Koniec operatorów ========== *)


(* struktura opisująca przedział [x, y] włącznie z x i y*)
type interval = int * int;;


(* ========== Funkcje pomocnicze dla przedziałów ========== *)


(* funkcja porównująca dwa przedziały 
   jeśli (a, b) > (c, d) zwraca 1
   jeśli (a, b) < (c, d) zwraca -1 
   w przypadku gdy się przecinają zwraca 0 
   interval -> interval -> int *)
let cmp (a, b) (c, d) = 
  if b < c then -1
  else if d < a then 1
  else 0;;

(* funkcja zwracająca ilość liczb całkowitych w przedziale;
   zabezpieczenie dla przypadku, gdy a = min_int
   (-min_int wykracza poza zakres int)
   interval -> int *)
let count_in_interval (a, b) =  
  if a = min_int then 
    if b = min_int then 1
    else b + max_int +2
  else b + (-a) + 1;; 

(* funkcja sprawdzająca czy liczba znajduje się w przedziale
   int -> interval -> bool *)
let in_interval x (a, b) = a <= x && x <= b;;


(* ========== Koniec funkcji pomocniczych ========== *)


(* struktura węzła drzewa zawierająca
   a) Pusty węzeł
   b) Węzeł z wartościami:
   - value: zakres przechowywany w węźle
   - left: lewe poddrzewo
   - right: prawe poddrzewo 
   - height: odległość od najdalszego liścia 
   - no_values: ilość liczb całkowitych w przedziale
     i przedziałach wszystkich węzłów obu poddrzew *)
type t = 
    Empty |
    Node of {
      value: interval;
      left: t;
      right: t;
      height: int;
      no_values: int;
    };;


(* ========== Funkcje pomocnicze ========== *)


(* funkcja zwracająca wysokość drzewa 
   t -> int *)
let get_height t =
  match t with
    Empty -> 0 |
    Node x -> x.height;;

(* funkcja zwracająca ilość różnych wartości
   we wszystkich zakresach na drzewie 
   t -> int *)
let get_no_values t =
  match t with
    Empty -> 0 |
    Node x -> x.no_values;;


(* funkcja tworząca nowe drzewo 
   l -> lewe poddrzewo
   r -> prawe poddrzewo 
   k -> zakres wartości w korzeniu 
   wysokość i liczba różnych wartości jest obliczana dla danych l k r 
   t -> interval -> t -> t *)
let make l k r = Node {value = k; left = l; right = r; 
                       height = (max (get_height l) (get_height r)) + 1;
                       no_values = (count_in_interval k) + get_no_values l + get_no_values r};;

(* funkcja balansująca drzewo;
   poprawia poddrzewa tak, aby wynik był drzewem AVL BST
   t -> interval -> t -> t *)
let bal l k r =
  let hl = get_height l and
  hr = get_height r in
  if hl > hr + 2 then
    match l with 
      Empty -> assert false |
      Node x -> 
      if (get_height x.left) >= (get_height x.right) then (make x.left x.value (make x.right k r))
      else
        match x.right with
          Empty -> assert false |
          Node y -> make (make x.left x.value y.left) y.value (make y.right k r)

  else if hr > hl + 2 then
    match r with
      Empty -> assert false |
      Node x -> 
      if (get_height x.right) >= (get_height x.left) then (make (make l k x.left) x.value x.right)
      else
        match x.left with
          Empty -> assert false |
          Node y -> make (make l k y.left) y.value (make y.right x.value x.right)        

  else make l k r;;

(* funkcja dodająca przedział k do drzewa; 
   działa jedynie gdy przedział k nie powinien zostać złączony
   z żadnym innym przedziałem w drzewie
   Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
   na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
   się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
   h ~ log(n), a więc funkcja działa w złożoności O(logn)
   interval -> t -> t*)
let rec add_one k = function
    Empty -> make Empty k Empty |
    Node x -> 
    let c = cmp k x.value in
    if c = 0 then Node {value = k; left = x.left; right = x.right; 
                        height = x.height; no_values = x.no_values}
    else if c < 0 then
      let nl = add_one k x.left in
      bal nl x.value x.right
    else
      let nr = add_one k x.right in
      bal x.left x.value nr;;

(* funkcja złączająca dwa drzewa i przedział w jedno drzewo 
   Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
   na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
   się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
   h ~ log(n), a więc funkcja działa w złożoności O(logn)
   t -> interval -> t -> t *)
let rec join l k r = 
  match (l, r) with
    (Empty, _) -> add_one k r |
    (_, Empty) -> add_one k l |
    (Node x, Node y) ->
    if x.height > y.height + 2 then bal x.left x.value (join x.right k r)
    else if y.height > x.height + 2 then bal (join l k y.left) y.value y.right
    else make l k r;;

(* funkcja zwracająca największy przedział w drzewie 
   Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
   na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
   się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
   h ~ log(n), a więc funkcja działa w złożoności O(logn)
   t -> interval *)
let rec max_elt = function
    Empty -> (max_int, max_int) |
    Node x -> if x.right = Empty then x.value else max_elt x.right;; 

(* funkcja zwracająca drzewo bez jego największego przedziału 
   Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
   na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
   się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
   h ~ log(n), a więc funkcja działa w złożoności O(logn)
   t -> t *)
let rec remove_max_elt = function
    Empty -> invalid_arg "ISet.remove_max_elt" |
    Node x -> if x.right = Empty then x.left else bal x.left x.value (remove_max_elt x.right);;

(* funkcja zwracająca najmniejszy przedział w drzewie 
   Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
   na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
   się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
   h ~ log(n), a więc funkcja działa w złożoności O(logn)
   t -> interval *)
let rec min_elt = function
    Empty -> (min_int, min_int) |
    Node x -> if x.left = Empty then x.value else min_elt x.left

(* funkcja zwracająca drzewo bez jego najmniejszego przedziału 
   Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
   na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
   się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
   h ~ log(n), a więc funkcja działa w złożoności O(logn)
   t -> t *)
let rec remove_min_elt = function
    Empty -> invalid_arg "ISet.remove_min_elt" |
    Node x -> if x.left = Empty then x.right else bal (remove_min_elt x.left) x.value x.right;; 

(* funkcja złączająca dwa drzewa w jedno  
   funkcja wywołuje min_elt i remove_min_elt które mają złożoność O(logn), 
   a więc sama działa w złożoności O(logn)
   t -> t -> t *)
let merge l r =
  match (l, r) with
    (Empty, _) -> r |
    (_, Empty) -> l |
    (Node x, Node y) ->
    let k = min_elt r in
    bal l k (remove_min_elt r);;

(* ========== Koniec funkcji pomocniczych ========== *)


(* pusty węzeł *)
let empty = Empty;;

(* funkcja zwracająca true jeśli węzeł jest pusty 
   t -> bool *)
let is_empty t = (t = Empty);;

(*  funkcja sprawdzająca, czy liczba k zawiera się w drzewie t 
    Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
    na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
    się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
    h ~ log(n), a więc funkcja działa w złożoności O(logn)    
    int -> t -> bool *)
let rec mem k t =
  match t with
    Empty -> false |
    Node x ->
    if (fst x.value > k) then mem k x.left
    else if (snd x.value < k) then mem k x.right
    else true    

(*  funkcja aplikująca funkcje f na wszystkich przedziałach w drzewie t.
    Przedziały są przekazywane do f w kolejności rosnącej. 
    (interval -> 'a) -> t -> unit *)
let iter f t =
  let rec loop = function
      Empty -> () |
      Node x -> loop x.left; f x.value; loop x.right

  in loop t;;

(* funkcja obliczająca [(f xN ... (f x2 (f x1 a))...)], gdzie x1
    ... xN to wszystkie kolejne przedziały t w kolejności rosnącej 
    (interval -> 'a -> 'a) -> t -> 'a -> 'a *)
let fold f t acc =
  let rec loop acc = function
      Empty -> acc |
      Node x -> loop (f x.value (loop acc x.left)) x.right

  in loop acc t;;

(* funkcja zwracająca listę wszystkich kolejnych przedziałów drzewa t
   Elementy listy są posortowane w kolejności rosnącej.
   t -> interval list *)
let elements t =
  let rec loop acc = function
      Empty -> acc |
      Node x -> loop (x.value :: loop acc x.right) x.left

  in loop [] t;;

(*  funkcja zwracająca [(l, present, r)], gdzie
    [l] to drzewo zawierające elementy [t] ostro mniejsze niż [k];
    [r] to drzewo zawierające elementy [t] ostro większe niż [k];
    [present] to [false] gdy [t] nie zawiera elementu równy [k],
    lub [true] gdy [t] zawiera element równy [k].
    Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
    na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
    się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
    h ~ log(n), a więc funkcja działa w złożoności O(logn)
    interval -> t -> t * bool * t  *)
let split k t =
  let rec loop = function
      Empty -> (Empty, false, Empty) |
      Node x ->
      let c = cmp (k, k) x.value in
      if c = 0 then
        let left = 
          if (fst x.value) = k then x.left
          else (add_one (fst x.value, k - 1) x.left)
        and right =
          if (snd x.value) = k then x.right
          else (add_one (k+1, snd x.value) x.right) in
        (left, true, right)
      else if c < 0 then 
        let (ll, present, rl) = loop x.left
        in (ll, present, join rl x.value x.right)
      else 
        let (lr, present, rr) = loop x.right
        in (join x.left x.value lr, present, rr)

  in loop t;;

(* funkcja zwracająca ilość liczb całkowitych 
   zawierających się w [t], mniejszych lub równych [n].
   Jeśli jest więcej niż max_int 
   liczb całkowitych mniejszych lub równych [n],
   funkcja zwróci max_int. 
   Funkcja w każdym wywołaniu rekurencyjnym wywołuje się maksymalnie
   na jednym synu aktualnie rozważanego węzła, w takim razie może wywołać 
   się maksymalnie h razy, gdzie h to odległość od korzenia do najdalszego liścia
   h ~ log(n), a więc funkcja działa w złożoności O(logn)
   int -> t -> int -> int *)
let below n t =
  let rec loop = function
    (* puste drzewo zawiera 0 elementów mniejszych
       niż cokolwiek *)
      Empty -> 0 |
      Node x ->
      (* Jeśli n zawiera się w x.value to wynikiem 
         będzie liczba elementów w lewym poddrzewie 
         i liczba elementów w x.value mniejszych lub równych n *)
      if cmp (n, n) x.value = 0 then
        (get_no_values x.left) + count_in_interval(fst x.value, n)
        (* Jeśli x jest mniejszy od każdego elementu w x.value 
           to sprawdzamy lewe poddrzewo *)
      else if cmp (n, n) x.value < 0 then loop x.left
      (* Jeśli x jest większy od każdego elementu w x.value 
         to sprawdzamy prawe poddrzewo i do wyniku w nim dodajemy 
         ilość elementów w lewym poddrzewie i w x.value *)
      else (get_no_values x.left) + (count_in_interval x.value) + (loop x.right)

  in loop t;;

(* funkcja usuwająca przedział k z drzewa t 
    funkcja wywoluje 2 razy split (O(logn)) i merge (O(logn))
    a więc działa w złożoności O(logn)
   interval -> t -> t *)
let remove k t =
  (* dzielimy drzewo t na dwa drzewa:
     l zawierające elementy ostro mniejsze niż k
     r zawierające elementy ostro większe niż k
     następnie łączymy l i r*)
  let (l, _, _) = split (fst k) t and
  (_, _, r) = split (snd k) t in
  merge l r;;

(* funkcja zwracająca drzewo zawierające elementy [t]
    oraz wszystkie elementy zakresu [x, y] włącznie z x i y.
    zakładam [x <= y]. 
    funkcja wywołuej split (O(logn)), mem (O(logn)), min_elt (O(logn)),
    remove_min_elt (O(logn)), max_elt (O(logn)), remove_max_elt (O(logn))
    a więc działa w złożoności O(logn)
    interval -> t -> t *)
let add (x, y) t =
  (* wyznaczamy drzewo l zawierające elementy ostro mniejsze niż
     najmniejszy w dodawanym zakresie *)
  let (l, _ , r) = split x t in
  (* wyznaczamy drzewo rr zawierające elementy ostro większe niż
     największy w dodawanym zakresie *)
  let (_, _, rr) = split y r in
  let (a, l) = 
    (* jeśli (x - 1) zawiera się w l to musimy dokleić
       największy przedział w l i usunąć go z l 
       (największy przedział będzie postaci [a, x-1]) *)
    if mem (x - 1) l then
      (fst (max_elt l), remove_max_elt l)
    else (x, l) in
  let (b, rr) =
    (* jeśli (x + 1) zawiera się w rr to musimy dokleić
       najmniejszy przedział w rr i usunąć go z rr 
       (największy przedział będzie postaci [x+1, b]) *)
    if mem (y + 1) rr then
      (snd (min_elt rr), remove_min_elt rr)
    else (y, rr) in

  bal l (a, b) rr;;