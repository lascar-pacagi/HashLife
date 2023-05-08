let find_default h x d = 
  match Hashtbl.find_opt h x with 
  | None -> d 
  | Some y -> y

let rec zip l1 l2 =
  match l1, l2 with 
  | [], _ | _, [] -> []
  | e1 :: r1, e2 :: r2 ->
      (e1, e2) :: zip r1 r2

[@@@ocaml.warning "-32"]
let baseline_life pts =
  let inc h x =
    let n = find_default h x 0 in 
    Hashtbl.replace h x (n + 1)
  in
  let counter =
    let h = Hashtbl.create (List.length pts) in
    pts 
    |> List.iter (fun (x, y) ->
      for dx = -1 to 1 do 
        for dy = -1 to 1 do 
          inc h (x + dx, y + dy) 
        done
      done
    );
    h
  in
  counter
  |> Hashtbl.to_seq
  |> List.of_seq
  |> List.map fst
  |> List.filter (fun pt ->
    let n = Hashtbl.find counter pt in 
    n = 3 || (n = 4 && List.mem pt pts) 
  )

(*
  +----+----+
  | ul | ur |
  +----+----+
  | ll | lr |
  +----+----+
*)
type quadtree = 
| Zero 
| One
| Q of { population : int; level : int; hash : string; ul : quadtree; ur : quadtree; ll : quadtree; lr : quadtree } 

let population q =
  match q with
  | Zero -> 0
  | One  -> 1
  | Q { population; _ } -> population

let hash q = 
  match q with
  | Zero -> "0" |> Digest.string
  | One  -> "1" |> Digest.string
  | Q { hash; _ } -> hash 

let level q = 
  match q with
  | Zero -> 0
  | One  -> 0
  | Q { level; _ } -> level
  
let size q =
  1 lsl level q

exception Undefined_behaviour of string

let ul q = 
  match q with 
  | Q { ul; _ } -> ul 
  | Zero | One -> raise @@ Undefined_behaviour "ul"

let ur q = 
  match q with 
  | Q { ur; _ } -> ur 
  | Zero | One -> raise @@ Undefined_behaviour "ur"

let ll q = 
  match q with 
  | Q { ll; _ } -> ll 
  | Zero | One -> raise @@ Undefined_behaviour "ll"

let lr q = 
  match q with 
  | Q { lr; _ } -> lr 
  | Zero | One -> raise @@ Undefined_behaviour "lr"

let ( --> ) f g = fun x -> g (f x)

let join ul ur ll lr =
  let population = population ul + population ur + population ll + population lr in
  let level = level ul + 1 in 
  Q { 
    population;          
    level;
    hash = string_of_int population
            ^ string_of_int level
            ^ hash ul
            ^ hash ur
            ^ hash ll
            ^ hash lr
           |> Digest.string;
    ul; ur; ll; lr;
  }

let rec zero k =
  if k = 0 then Zero 
  else 
    let z = zero (k - 1) in 
    join z z z z 

let center q =
  match q with 
  | Zero | One -> raise @@ Invalid_argument "center"
  | _ ->
      let z = zero (level q - 1) in
      join 
        (join z z z (ul q))
        (join z z (ur q) z)
        (join z (ll q) z z)
        (join (lr q) z z z)

let inner q =
  match q with
  | Zero | One -> raise @@ Invalid_argument "inner"
  | _ ->
      join 
        ((ul --> lr) q)
        ((ur --> ll) q)
        ((ll --> ur) q)
        ((lr --> ul) q)

let life q11 q12 q13 
         q21 c   q23
         q31 q32 q33 =
  let outer =     
    [q11; q12; q13; q21; q23; q31; q32; q33]
    |> List.map population
    |> List.fold_left (+) 0 
  in
  if outer = 3 || outer = 2 && c = One then 
    One
  else 
    Zero

let life_4x4 q =
  (*
    aa ab ba bb
    ac ad bc bd
    ca cb da db
    cc cd dc dd   
  *)
  let a = ul q in
  let aa = ul a and ab = ur a and ac = ll a and ad = lr a in
  let b = ur q in
  let ba = ul b and bb = ur b and bc = ll b and bd = lr b in
  let c = ll q in
  let ca = ul c and cb = ur c and cc = ll c and cd = lr c in
  let d = lr q in
  let da = ul d and db = ur d and dc = ll d and dd = lr d in
  join 
    (life aa ab ba ac ad bc ca cb da)
    (life ab ba bb ad bc bd cb da db)
    (life ac ad bc ca cb da cc cd dc)
    (life ad bc bd cb da db cd dc dd)
  
let rec expand ?(x = 0) ?(y = 0) ?(clip = None) ?(lvl = 0) q =
  if population q = 0 then
    [] 
  else 
    begin 
      let length = 1 lsl (level q) in
      if level q = lvl then
        let gray = (population q |> float_of_int) /. (float_of_int length) ** 2.0 in
        [(x lsr lvl, y lsr lvl), gray]
      else
        let offset = length lsr 1 in 
        match clip with 
        | Some (xmin, xmax, ymin, ymax) when (x + length < xmin || x > xmax) && (y + length < ymin || y > ymax) ->
            [] 
        | _ ->
            expand ~x ~y:(y + offset) ~clip ~lvl (ul q)
            @ expand ~x:(x + offset) ~y:(y + offset) ~clip ~lvl (ur q)
            @ expand ~x ~y ~clip ~lvl (ll q)
            @ expand ~x:(x + offset) ~y ~clip ~lvl (lr q)
    end

let construct pts =
  let xmin =
    pts |> List.map fst |> List.fold_left min max_int
  in
  let ymin = 
    pts |> List.map snd |> List.fold_left min max_int
  in
  let quadtrees = 
    pts |> List.map (fun (x, y) -> (x - xmin, y - ymin), One)
  in
  let rec construct lvl quadtrees =
    match quadtrees with 
    | [] -> assert false
    | [(_, q)] -> q
    | _ -> 
      let z = zero lvl in
      let coord2q = 
        let h = Hashtbl.create (List.length quadtrees) in
        quadtrees |> List.iter (fun ((x, y), q) -> Hashtbl.add h (x, y) q);
        h
      in
      let seen = Hashtbl.create (List.length quadtrees) in
      quadtrees
      |> List.map (fun ((x, y), _) -> 
          if not @@ Hashtbl.mem seen (x, y) then
            begin
              let x = x - (x land 1) in
              let y = y - (y land 1) in
              let ul = find_default coord2q (x, y + 1) z in 
              let ur = find_default coord2q (x + 1, y + 1) z in 
              let ll = find_default coord2q (x, y) z in
              let lr = find_default coord2q (x + 1, y) z in 
              Hashtbl.add seen (x, y) ();
              Hashtbl.add seen (x + 1, y) ();
              Hashtbl.add seen (x, y + 1) ();
              Hashtbl.add seen (x + 1, y + 1) ();
              [(x lsr 1, y lsr 1), join ul ur ll lr]
            end
          else [])
      |> List.flatten
      |> construct (lvl + 1)
  in
  (xmin, ymin), construct 0 quadtrees

let memo_successor = Hashtbl.create 1503713

(*
  aaa aab aba abb  baa bab bba bbb
  aac aad abc abd  bac bad bbc bbd
  aca acb ada adb  bca bcb bda bdb
  acc acd adc add  bcc bcd bdc bdd
 
  caa cab cba cbb  daa dab dba dbb
  cac cad cbc cbd  dac dad dbc dbd
  cca ccb cda cdb  dca dcb dda ddb
  ccc ccd cdc cdd  dcc dcd ddc ddd
*)
(*
  aaa aab aba abb  baa bab bba bbb
  aac q1  q1  q2   q2  q3  q3  bbd
  aca q1  q1  q2   q2  q3  q3  bdb
  acc q4  q4  q5   q5  q6  q6  bdd
 
  caa q4  q4  q5   q5  q6  q6  dbb
  cac q7  q7  q8   q8  q9  q9  dbd
  cca q7  q7  q8   q8  q9  q9  ddb
  ccc ccd cdc cdd  dcc dcd ddc ddd
*)
let rec successor ?(j = max_int) q =
  let h = (j, hash q) in
  match Hashtbl.find_opt memo_successor h with
  | Some res -> res
  | None ->
      let join' f1 f2 f3 f4 q =
        join (f1 q) (f2 q) (f3 q) (f4 q) 
      in
      let res =
        match q with
        | Zero | One -> Zero 
        | _ when population q = 0 -> ul q 
        | _ when level q = 2 -> life_4x4 q 
        | _ ->
            let q1 = successor ~j (ul q) in 
            let q2 = successor ~j (join' (ul --> ur) (ur --> ul) (ul --> lr) (ur --> ll) q) in
            let q3 = successor ~j (ur q) in
            let q4 = successor ~j (join' (ul --> ll) (ul --> lr) (ll --> ul) (ll --> ur) q) in 
            let q5 = successor ~j (join' (ul --> lr) (ur --> ll) (ll --> ur) (lr --> ul) q) in
            let q6 = successor ~j (join' (ur --> ll) (ur --> lr) (lr --> ul) (lr --> ur) q) in
            let q7 = successor ~j (ll q) in 
            let q8 = successor ~j (join' (ll --> ur) (lr --> ul) (ll --> lr) (lr --> ll) q) in
            let q9 = successor ~j (lr q) in
            if j >= level q - 2 then
              join 
                (successor ~j (join q1 q2 q4 q5))
                (successor ~j (join q2 q3 q5 q6))
                (successor ~j (join q4 q5 q7 q8))
                (successor ~j (join q5 q6 q8 q9))
            else     
              join
                (join (lr q1) (ll q2) (ur q4) (ul q5))
                (join (lr q2) (ll q3) (ur q5) (ul q6))
                (join (lr q4) (ll q5) (ur q7) (ul q8))
                (join (lr q5) (ll q6) (ur q8) (ul q9))
        in
        Hashtbl.add memo_successor h res;
        res

let explode n = 
  let rec explode i n =
    if n = 0 then 
      []
    else
      (i, n land 1) :: explode (i + 1) (n lsr 1)
  in
  explode 0 n 
  |> List.rev

let is_padded q =
  ul q |> population = ((ul --> lr --> lr) q |> population)
  && ur q |> population = ((ur --> ll --> ll) q |> population)
  && ll q |> population = ((ll --> ur --> ur) q |> population)
  && lr q |> population = ((lr --> ul --> ul) q |> population)
  
let rec pad q =
  if level q <= 3 || not (is_padded q) then 
    center q 
    |> pad
  else
    q 

let rec crop q =
  if level q <= 3 || not (is_padded q) then
    q 
  else 
    inner q 
    |> crop

let rec reduce q =
  let nobody l = List.for_all (fun q -> population q = 0) l in
  match q with 
  | Q { ul; ur; ll; lr; _ } when nobody [ur; ll; lr] -> reduce ul 
  | Q { ul; ur; ll; lr; _ } when nobody [ul; ll; lr] -> reduce ur
  | Q { ul; ur; ll; lr; _ } when nobody [ul; ur; lr] -> reduce ll
  | Q { ul; ur; ll; lr; _ } when nobody [ul; ur; ll] -> reduce lr
  | _ -> q    

let advance n q =
  match q with 
  | _ when n = 0 -> q 
  | Zero | One -> Zero
  | _ ->  
      explode n
      |> List.fold_left (fun acc (j, bit) ->
        if bit = 1 then 
          pad acc 
          |> successor ~j
        else acc 
      ) q
   
[@@@ocaml.warning "-32"]
let rec ffw n q =
  if n = 0 then q 
  else 
    pad q 
    |> successor
    |> ffw (n - 1)

module S = Set.Make(struct type t = int * int let compare = Stdlib.compare end)

let sleep s = 
  Unix.sleepf s

let cwd () =
  Unix.getcwd ()

let isdir name =
  let open Unix in
  match (stat name).st_kind with
  | S_DIR -> true 
  | _     -> false

let chdir name = 
  Unix.chdir name

let dir_entries name =
  if not @@ isdir name then raise @@ Invalid_argument "dir_entries";
  let open Unix in
  let handle = opendir name in
  let rec loop acc =
    try 
      (readdir handle) :: acc
      |> loop
    with End_of_file -> acc 
  in
  loop []
  |> List.sort Stdlib.compare

let join_string ?(sep = " ") l =
  let b = Buffer.create 16 in
  let rec loop = function
  | []  -> ()
  | [s] -> Buffer.add_string b s 
  | s :: r ->
      Buffer.add_string b s;
      Buffer.add_string b sep;
      loop r     
  in
  loop l;
  Buffer.contents b

let load filename =
  let input = open_in filename in
  let line_to_points x y acc line =
    let n = String.length line in
    let rec line_to_points x y acc i =
      if i = n then (x, y), acc 
      else
        match line.[i] with 
        | '*' -> line_to_points (x + 1) y ((x, y)::acc) (i + 1)
        | _   -> line_to_points (x + 1) y acc (i + 1)
    in
    match () with 
    | _ when n = 0 -> (x, y), acc 
    | _ when line.[0] = '#' && n = 1 -> (x, y), acc 
    | _ when line.[0] = '#' && line.[1] = 'P' ->
        let r = Str.regexp {|[ ]*\(-?[0-9]+\)[ ]*\(-?[0-9]+\)|} in
        if not @@ Str.string_match r line 2 then (x, y), acc 
        else
          begin
            try 
              let x, y =
                Str.matched_group 1 line |> int_of_string,
                Str.matched_group 2 line |> int_of_string
              in
              (x, y), acc
            with _ -> (x, y), acc
          end
    | _ when line.[0] = '#' -> (x, y), acc 
    | _ -> 
        let (_, y), acc = line_to_points x y acc 0 in 
        (x, y), acc       
  in
  let rec loop x y acc =
    try 
      let (x, y), acc =
        input_line input
        |> line_to_points x (y + 1) acc 
      in
      loop x y acc
    with End_of_file -> acc
  in
  let pts = loop 0 0 [] in
  close_in input;
  pts

type state = 
| MainMenu of { item : int }
| QuadtreeOptions of { item : int; xoffset : string; yoffset : string; stop_at_level : string; center : string }
| CellSize of { input : string }
| InputCells of { input : S.t }
| Simulation of { item : int; nb_steps : string; automatic : string; ms : string; executing : bool }
| Statistics
| Load of { item : int; filenames : string list }
| Help

type data = { 
  mutable cell_size : int; 
  mutable show_grid : bool;
  mutable quadtree : quadtree;
  mutable show_quadtree : bool;
  mutable xoffset : int;
  mutable yoffset : int;
  mutable stop_at_level : int;
  mutable center : bool; 
  mutable generations : int;
}

let default_cell_size = 10

let data = {
  cell_size = default_cell_size;
  show_grid = true;
  quadtree = Zero;
  show_quadtree = false;
  xoffset = 0;
  yoffset = 0;
  stop_at_level = 0;
  center = false;
  generations = 0;
}

let main_menu_name_list = [
  "Show quadtree"; 
  "Quadtree options"; 
  "Show grid"; 
  "Set cell size"; 
  "Input cells";
  "Simulation";
  "Statistics";
  "Load";
  "Help";
  "Quit";
]

let main_menu_names = 
  main_menu_name_list
  |> List.tl
  |> List.fold_left (fun acc s ->
      acc ^ "\n" ^ s
  ) (List.hd main_menu_name_list)

let main_menu_default_item = List.length main_menu_name_list - 2 

let state = ref (MainMenu { item = main_menu_default_item })
  
let cell_size_name = "Cell size: "

let quadtree_options_names = [
  "x offset: ";
  "y offset: ";
  "Stop at level: ";
  "Center: ";
]

let simulation_names = [
  "# of steps: ";
  "Automatic: ";
  "Milliseconds: ";
  "Simulation: ";
]

let help_message = {|Main menu:
  - Moving around menu:
      * Up:   Hit the 'w' key.
      * Down: Hit the 's' key.
  - Hit the 'q' key to close the current menu or action.
  - Select item:      Hit the 'enter' key.
  - Show quadtree:    Toggle the quadtree view.
  - Quadtree options: Center or offset the quadtree by a given (dx, dy).
                      You can also choose to cut the quadtree at a given level.
  - Show grid:        Toggle the grid view.
  - Set cell size:    Set the size, in pixel, of the cell side.
                      It will determine the size of the grid.
  - Input cells:      Use the mouse to set live cells by clicking
                      on the canvas. To erase a cell, just click on
                      it again.
  - Simulation:       Set simulation options and launch the game of life:
                        * # steps: Number of steps per iteration.
                        * Automatic: If No, you need to hit a key to advance
                                     in the game of life, otherwise, the simulation
                                     runs by itself.
                                     In any mode, to stop the simulation you need to hit
                                     the 'q' key.
                        * Milliseconds: In automatic mode, the number of
                                        milliseconds between each iterations.
                        * Start: Start the game of life.
  - Statistics:       Statistics about the quadtree and the memoization.
  - Load:             Load a file with format Life 1.05.
  - Help:             This menu.
  - Quit:             Quit the application.|}

let window_size = " 2200x1200"

let draw_grid size =
  let open Graphics in
  set_color black;
  if size <= 1 then ()
  else
    begin 
      let nx = (size_x () + size - 1) / size in 
      let ny = (size_y () + size - 1) / size in 
      let endx = nx * size in
      let endy = ny * size in
      for i = 0 to nx do
        let x = i * size in  
        moveto x 0;
        lineto x endy
      done;
      for i = 0 to ny do
        let y = i * size in 
        moveto 0 y;
        lineto endx y
      done
    end

let darkgreen = Graphics.rgb 0 100 0
let deepskyblue = Graphics.rgb 0 191 255

let clear () =
  let open Graphics in
  set_color darkgreen;
  clear_graph ();  
  fill_rect 0 0 (size_x ()) (size_y ());
  set_color black

let gray_level_to_rgb gray =
  let v = 255.0 *. (1.0 -. gray) |> int_of_float in
  Graphics.rgb v v v

let rec draw_quadtree ?(x = 0) ?(y = 0) ?(clip = None) ?(lvl = 0) ?(show_border = true) ?(size = 1) q =
  let open Graphics in
  let length = 1 lsl (level q) in  
  let xmin, xmax, ymin, ymax =
    match clip with 
    | Some (xmin, xmax, ymin, ymax) -> xmin, xmax, ymin, ymax
    | None -> min_int, max_int, min_int, max_int         
  in
  match () with 
  | _  when x + length < xmin || x > xmax || y + length < ymin || y > ymax -> ()
  | _ ->
      begin
        match q with 
        | Zero -> ()
        | One ->
            set_color black;
            fill_rect (x * size) (y * size) size size
        | Q { population; _ } when population = 0 -> ()    
        | Q { population; level; ul; ur; ll; lr; _ } ->             
            if level = lvl then
              begin
                (float_of_int population) /. (float_of_int length) ** 2.0 
                |> gray_level_to_rgb
                |> set_color;
                fill_rect (x * size) (y * size) (length * size) (length * size) 
              end
            else 
              begin
                let offset = length lsr 1 in
                draw_quadtree ~x ~y:(y + offset) ~clip ~lvl ~show_border ~size ul;
                draw_quadtree ~x:(x + offset) ~y:(y + offset) ~clip ~lvl ~show_border ~size ur;
                draw_quadtree ~x ~y ~clip ~lvl ~show_border ~size ll;
                draw_quadtree ~x:(x + offset) ~y ~clip ~lvl ~show_border ~size lr
              end
      end;
      if show_border then 
        begin
          set_color red;
          draw_rect (x * size) (y * size) (length * size) (length * size)
        end

let expand_visible q =
  let open Graphics in
  let csize = data.cell_size in
  let w, h = 
    (size_x () + csize - 1) / csize, (size_y () + csize - 1) / csize 
  in
  expand ~x:data.xoffset ~y:data.yoffset ~clip:(Some(0, w - 1, 0, h - 1)) ~lvl:0 q

let draw_message_in_box ?(cond = fun _ -> false) ?(condtrue = fun _ -> ()) ?(condfalse = fun _ -> ()) 
                        ?(visible = fun _ -> true) msg =
  let open Graphics in 
  let w = size_x () in
  let h = size_y () in
  let lines = String.split_on_char '\n' msg in
  let text_dims = 
    List.map text_size lines
  in
  let maxw =
    text_dims
    |> List.map fst
    |> List.fold_left max 0
  in
  let maxh =
    text_dims
    |> List.map snd
    |> List.fold_left max 0
  in
  let margin = 20 in
  let newline = 5 in
  let boxw = 2 * margin + maxw  in 
  let n = 
    lines
    |> List.filteri (fun i _ -> visible i)
    |> List.fold_left (fun acc _ -> acc + 1) 0     
  in  
  let boxh = 2 * margin + n * maxh + (n - 1) * newline in
  let x, y = (w - boxw) / 2, (h - boxh) / 2 in  
  set_color deepskyblue;
  fill_rect x y boxw boxh;
  set_line_width 5;
  set_color black;
  draw_rect x y boxw boxh;
  set_line_width 1;
  lines
  |> List.rev
  |> List.fold_left (fun (i, x, y) item ->
      if not @@ visible i then (i - 1, x, y)
      else 
        begin
          if cond i then condtrue i
          else condfalse i;
          moveto x y;
          draw_string item;
          (i - 1, x, y + maxh + newline)
        end
  ) (List.length lines - 1, x + margin, y + margin)
  |> ignore
            
let draw_main_menu sel =
  let open Graphics in
  draw_message_in_box ~cond:((=) sel) ~condtrue:(fun _ -> set_color yellow) ~condfalse:(fun _ -> set_color black) main_menu_names

let draw_load_file sel filenames =
  let n = List.length filenames in
  let around = 5 in
  let visible i =
    if sel <= around then i <= around * 2 
    else if sel >= n - around then i >= n - 2 * around - 1
    else i >= sel - around && i <= sel + around
  in
  let open Graphics in
  filenames
  |> join_string ~sep:"\n"
  |> draw_message_in_box ~cond:((=) sel) ~condtrue:(fun _ -> set_color yellow) ~condfalse:(fun _ -> set_color black) ~visible

let draw_cell_size input =
  let open Graphics in 
  let w = size_x () in
  let h = size_y () in
  let textw, texth = text_size cell_size_name in
  let inputw, inputh = 
    let inputw, inputh = text_size input in 
    (max textw inputw, max texth inputh)  
  in
  let margin = 10 in
  let boxw = 2 * margin + textw + inputw in 
  let boxh = 2 * margin + max texth inputh in
  let x, y = (w - boxw) / 2, (h - boxh) / 2 in  
  set_color deepskyblue;
  fill_rect x y boxw boxh;
  set_line_width 5;
  set_color black;
  draw_rect x y boxw boxh;
  set_line_width 1;
  moveto (x + margin) (y + margin);
  draw_string cell_size_name;
  moveto (x + margin + textw) (y + margin);
  draw_string input

let draw_help () = 
  draw_message_in_box help_message  

let draw_option_list sel names fields =
  let open Graphics in 
  let w = size_x () in
  let h = size_y () in
  let names_and_inputs =
    zip names fields
    |> List.rev
  in
  let dims =
    names_and_inputs
    |> List.map (fun (name, input) ->
      let textw, texth = text_size name in 
      let inputw, inputh = text_size input in         
      (textw, texth), (inputw, inputh)
    )
  in
  let margin = 10 in
  let boxw, boxh =
    dims
    |> List.fold_left (fun (boxw, boxh) ((textw, texth), (inputw, inputh)) ->
        (max boxw (3 * margin + textw + max textw inputw), boxh + margin + max texth inputh)
    ) (0, margin)
  in 
  let x, y = (w - boxw) / 2, (h - boxh) / 2 in
  set_color deepskyblue;
  fill_rect x y boxw boxh;
  set_line_width 5;
  set_color black;
  draw_rect x y boxw boxh;
  set_line_width 1;
  zip names_and_inputs dims
  |> List.fold_left (fun (i, x, y) ((name, input), ((textw, texth), (_, inputh))) ->
    moveto (x + margin) y;
    draw_string name;
    moveto (x + margin + textw) y;
    if i = sel then set_color yellow;
    draw_string input;
    set_color black;
    (i - 1, x, y + margin + max texth inputh)  
  ) (List.length names - 1, x, y + margin)
  |> ignore;
  set_color black
  
let draw_cells ?(color = Graphics.black) cells =
  let open Graphics in
  set_color color;
  cells
  |> List.iter (fun (x, y) ->
    fill_rect (x * data.cell_size) (y * data.cell_size) data.cell_size data.cell_size
  )

let draw_statistics () =
  Printf.sprintf 
{|Statistics:
  - Quadtree size       : %d
  - Quadtree # of levels: %d
  - # of cells          : %d
  - # of generations    : %d
  - Memoization size    : %d|}
  (size data.quadtree)
  (level data.quadtree)
  (population data.quadtree)
  data.generations
  (Hashtbl.length memo_successor)
  |> draw_message_in_box

let offset_to_center_quadtree () =
  let open Graphics in 
  let m = size data.quadtree / 2 in
  data.xoffset <- size_x () / data.cell_size / 2 - m;
  data.yoffset <- size_y () / data.cell_size / 2 - m
  
let draw () =
  Graphics.auto_synchronize false;
  clear ();
  if data.show_grid then draw_grid data.cell_size;
  let csize = data.cell_size in
  let w, h = 
    (Graphics.size_x () + csize - 1) / csize, (Graphics.size_y () + csize - 1) / csize 
  in
  if data.center then offset_to_center_quadtree ();
  draw_quadtree ~x:data.xoffset ~y:data.yoffset ~clip:(Some(0, w - 1, 0, h - 1))
                ~lvl:data.stop_at_level ~show_border:data.show_quadtree
                ~size:data.cell_size data.quadtree;
  begin
    match !state with 
    | MainMenu { item } ->
        draw_main_menu item 
    | QuadtreeOptions { item; xoffset; yoffset; stop_at_level; center } ->
        draw_option_list item quadtree_options_names [xoffset; yoffset; stop_at_level; center ]
    | CellSize { input } ->
        draw_cell_size input
    | InputCells { input } ->
        input
        |> S.to_seq
        |> List.of_seq
        |> List.map (fun (x, y) -> (x + data.xoffset, y + data.yoffset))
        |> draw_cells ~color:Graphics.yellow
    | Simulation { item; nb_steps; automatic; ms; executing } ->
        if not executing then draw_option_list item simulation_names [nb_steps; automatic; ms; "Start"]
    | Statistics ->
        draw_statistics ()
    | Load { item; filenames } ->
        draw_load_file item filenames
    | Help ->
        draw_help ()
  end;
  Graphics.auto_synchronize true

let backspace s =
  if String.length s = 1 then ""
  else String.sub s 0 (String.length s - 1)

let minus s =
  try 
    if s = "" || s = "0" then "-"
    else if String.get s 0 = '-' then String.sub s 1 (String.length s - 1)
    else "-" ^ s
  with Invalid_argument _ -> s 

let add_digit n d =
  (if n = "0" then "" else n) ^ String.make 1 d

let empty_to_default ?(d = 0) input =
  if input = "" then string_of_int d
  else input
  
let handle_event status = 
  let open Graphics in
  match !state with 
    | MainMenu { item } ->
        let on_enter = [|
            (fun () -> data.show_quadtree <- not data.show_quadtree);
            (fun () -> state := QuadtreeOptions { 
                                  item = 0;
                                  xoffset = data.xoffset |> string_of_int; 
                                  yoffset = data.yoffset |> string_of_int; 
                                  stop_at_level = data.stop_at_level |> string_of_int;
                                  center = if data.center then "Yes" else "No"
                                });
            (fun () -> data.show_grid <- not data.show_grid);
            (fun () -> state := CellSize { input = "" });
            (fun () ->
              data.generations <- 0;
              let cells = 
                data.quadtree
                |> expand_visible 
                |> List.map (fun ((x, y), _) -> (x - data.xoffset, y - data.yoffset))                 
              in
              state := InputCells { input = S.of_list cells }
            );
            (fun () -> state := Simulation { item = 0; nb_steps = "1"; automatic = "No"; ms = "_"; executing = false });
            (fun () -> state := Statistics);
            (fun () -> state := Load { item = 0; filenames = dir_entries "." });
            (fun () -> state := Help);
            (fun () -> raise_notrace Exit);   
          |]
        in
        if status.keypressed then 
          begin          
            let n = List.length main_menu_name_list in
            match status.key with
            | 's' -> state := MainMenu { item = (item + 1) mod n }
            | 'w' -> state := MainMenu { item = (item - 1 + n) mod n }
            | '\r' -> on_enter.(item)()
            | 'q'  -> raise_notrace Exit            
            | _ -> ()
          end
    | QuadtreeOptions ({ item; xoffset; yoffset; stop_at_level; center } as options) ->
        if status.keypressed then 
          begin          
            let n = List.length quadtree_options_names in
            match status.key with
            | 's' -> state := QuadtreeOptions { options with item = (item + 1) mod n }
            | 'w' -> state := QuadtreeOptions { options with item = (item - 1 + n) mod n }
            | '\b' ->
              begin
                try 
                  match item with
                  | 0 -> state := QuadtreeOptions { options with xoffset = backspace xoffset |> empty_to_default }
                  | 1 -> state := QuadtreeOptions { options with yoffset = backspace yoffset |> empty_to_default }
                  | 2 -> state := QuadtreeOptions { options with stop_at_level = backspace stop_at_level |> empty_to_default }
                  | _ -> ()
                with Invalid_argument _ -> ()
              end
            | '-' when item = 0 ->
                state := QuadtreeOptions { 
                  options with xoffset = minus xoffset 
                }
            | '-' when item = 1 ->
                state := QuadtreeOptions { 
                  options with yoffset = minus yoffset 
                }
            | '0'..'9' as d when item = 0 -> 
                state := QuadtreeOptions { 
                  options with xoffset = add_digit xoffset d 
                }
            | '0'..'9' as d when item = 1 -> 
                state := QuadtreeOptions { 
                  options with yoffset = add_digit yoffset d
                }
            | '0'..'9' as d when item = 2 -> 
                state := QuadtreeOptions { 
                  options with stop_at_level = add_digit stop_at_level d
                }
            | '\r' when item = 0 ->
                data.xoffset <- (try int_of_string xoffset with _ -> 0);
                state := QuadtreeOptions {
                  options with item = (item + 1) mod n
                }
            | '\r' when item = 1 ->
                data.yoffset <- (try int_of_string yoffset with _ -> 0);
                state := QuadtreeOptions {
                  options with item = (item + 1) mod n
                } 
            | '\r' when item = 2 ->
                data.stop_at_level <- (try int_of_string stop_at_level with _ -> 0);
                state := QuadtreeOptions {
                  options with item = (item + 1) mod n
                }
            | '\r' when item = 3 ->
                data.center <- center = "No";
                if data.center then offset_to_center_quadtree ()
                else
                  begin
                    data.xoffset <- 0;
                    data.yoffset <- 0                    
                  end;   
                let xoffset, yoffset = 
                  string_of_int data.xoffset, string_of_int data.yoffset
                in
                state := QuadtreeOptions {
                  options with center = if data.center then "Yes" else "No"; xoffset; yoffset
                }
            | '\r' -> 
                state := QuadtreeOptions {
                  options with item = (item + 1) mod n
                }
            | 'q' ->
                data.xoffset <- (try int_of_string xoffset with _ -> 0);
                data.yoffset <- (try int_of_string yoffset with _ -> 0);
                data.stop_at_level <- (try int_of_string stop_at_level with _ -> 0);
                state := MainMenu { item = main_menu_default_item }            
            | _ -> ()
          end
    | CellSize { input } ->
        if status.keypressed then
          begin
            match status.key with 
            | '0'..'9' as d -> state := CellSize { input = input ^ String.make 1 d }
            | '\b' -> 
              begin 
                try 
                  state := CellSize { input = backspace input }
                with Invalid_argument _ -> () 
              end
            | '\r' -> 
                data.cell_size <- (try int_of_string input with _ -> default_cell_size)
            | 'q' ->
                state := MainMenu { item = main_menu_default_item }
            | _ -> ()
          end
    | InputCells { input } ->        
        if status.button then
          begin 
            let x, y = status.mouse_x / data.cell_size - data.xoffset, status.mouse_y / data.cell_size - data.yoffset in 
            state := InputCells { input = (if S.mem (x, y) input then S.remove else S.add) (x, y) input }
          end
        else if status.keypressed then 
          begin
            match status.key with
            | 'q' ->
                let q =                  
                  if S.is_empty input then Zero
                  else
                    input
                    |> S.to_seq
                    |> List.of_seq
                    |> construct
                    |> snd
                in
                data.quadtree <- q;
                state := MainMenu { item = main_menu_default_item }
            | 'c' ->
                Hashtbl.reset memo_successor;
                state := InputCells { input = S.empty }
            | _ -> ()
          end          
    | Simulation ({ item; nb_steps; automatic; ms; _ } as options) ->
        if status.keypressed then 
          begin
            let n = simulation_names |> List.length in
            match status.key with 
            | 'q' -> state := MainMenu { item = main_menu_default_item }
            | 's' -> state := Simulation { options with item = (item + 1) mod n }
            | 'w' -> state := Simulation { options with item = (item - 1 + n) mod n }
            | '\r' when item = 0 || item = 2 -> state := Simulation { options with item = (item + 1) mod n }
            | '\r' when item = 1 && automatic = "No" -> 
                state := Simulation { options with automatic = "Yes"; ms = "500" }
            | '\r' when item = 1 && automatic = "Yes" -> 
                state := Simulation { options with automatic = "No"; ms = "_" }
            | '\r' when item = 3 && (automatic = "Yes" && ms <> "_" || automatic = "No" && nb_steps <> "0") ->
              begin
                try
                  state := Simulation { options with executing = true };
                  draw ();
                  let nb_steps = int_of_string nb_steps in
                  let auto = automatic = "Yes" in
                  let seconds = try (ms |> int_of_string |> float_of_int) /. 1000.0 with Failure _ -> 0.0 in
                  while true do                                         
                    if auto then 
                      begin
                        let status = wait_next_event [Poll] in 
                        if status.keypressed && status.key = 'q' then 
                          begin
                            wait_next_event [Key_pressed] |> ignore; 
                            raise_notrace Exit
                          end;                        
                        data.quadtree <- advance nb_steps data.quadtree |> crop |> reduce;
                        data.generations <- data.generations + nb_steps;
                        draw ();
                        if seconds <> 0.0 then sleep seconds 
                      end
                    else
                      begin
                        let status = wait_next_event [Key_pressed] in
                        if status.keypressed then
                          match status.key with 
                          | 'q' -> raise_notrace Exit
                          | _   -> 
                              data.quadtree <- advance nb_steps data.quadtree |> crop |> reduce;
                              data.generations <- data.generations + nb_steps;
                              if nb_steps > 100 then
                                begin
                                  Printf.sprintf "%d steps done" nb_steps |> draw_message_in_box;
                                  sleep 0.5
                                end;
                              draw ()
                      end                      
                  done
                with Exit -> state := Simulation { options with executing = false }
              end
            | '\b' ->
              begin 
                try 
                  match item with
                  | 0 -> state := Simulation { options with nb_steps = backspace nb_steps |> empty_to_default }                      
                  | 2 -> state := Simulation { options with ms = backspace ms |> empty_to_default }
                  | _ -> ()
                with Invalid_argument _ -> ()
              end
            | '0'..'9' as d when item = 0 -> 
                state := Simulation { 
                  options with nb_steps = add_digit nb_steps d 
                }
            | '0'..'9' as d when item = 2 -> 
                state := Simulation { 
                  options with ms = add_digit ms d 
                }
            | _ -> ()                
          end
    | Statistics ->
        if status.keypressed && status.key = 'q' then
          state := MainMenu { item = main_menu_default_item }
    | Load ({ item; filenames } as options) -> 
        if status.keypressed then 
          begin
            let n = filenames |> List.length in
            match status.key with 
            | 'q'  -> state := MainMenu { item = main_menu_default_item }
            | 's'  -> state := Load { options with item = (item + 1) mod n }
            | 'w'  -> state := Load { options with item = (item - 1 + n) mod n }
            | '\r' -> 
              let file = List.nth filenames item in
              if isdir file then
                begin
                  chdir file;
                  state := Load { item = 0; filenames = dir_entries "." }
                end
              else
                begin
                  Hashtbl.reset memo_successor;
                  data.generations <- 0; 
                  let q =                  
                    let pts = load file in
                    if pts = [] then Zero
                    else
                      pts
                      |> construct
                      |> snd
                  in                
                  data.quadtree <- q
                end
            | _ -> ()
          end
    | Help ->
        state := MainMenu { item = main_menu_default_item }

let () = 
  let open Graphics in
  open_graph window_size;
  set_font "-*-fixed-medium-r-semicondensed--25-*-*-*-*-*-iso8859-1";
  set_window_title "HashLife";
  draw ();
  try
    while true do
      let status = wait_next_event [Key_pressed; Button_down; Button_up] in
      handle_event status;
      draw ()
    done
  with Exit -> close_graph ()
