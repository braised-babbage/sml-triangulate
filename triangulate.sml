type point = int * int

(* twice the ~signed area~ of the triangle *)
fun area2((x1,y1) : point, (x2,y2) : point, (x3,y3) : point)
  = (x2-x1)*(y3-y1) - (x3-x1)*(y2-y1)

(* is c to the left of the line spanned by a,b *)
fun left(a,b,c) = area2(a,b,c) > 0;

fun collinear(a,b,c) = area2(a,b,c) = 0;

fun leftOn(a,b,c) = area2(a,b,c) >= 0;


(* do the segments ab and cd intersect 
 * at a point interior to both *)
fun properIntersection(a,b,c,d) =
  (* eliminate improper cases *)
  (not (collinear(a,b,c) orelse
	collinear(a,b,d) orelse
	collinear(c,d,a) orelse
	collinear(c,d,b)))
  andalso (* c and d should be on opposite sides of ab *)
  left(a,b,c) <> left(a,b,d)
  andalso
  left(c,d,a) <> left(c,d,b)

(* does c lay on the segment ab *)
fun between(a as (x1,y1) : point,
	    b as (x2,y2) : point,
	    c as (x3,y3) : point) =
  collinear(a,b,c) andalso
  (* if the segment ab is not vertical... *)
  if x1 <> x2
  then (x1 <= x3 andalso x3 <= x2)
       orelse (x1 >= x3 andalso x3 >= x2)
  else (y1 <= y3 andalso y3 <= y2)
       orelse (y1 >= y3 andalso y3 >= y2)

(* do the segments ab and cd intersect *)		  
fun intersection(a,b,c,d) =

  (* an intersection is either 
   *   i) proper
   *   ii) improper          *)
  properIntersection(a,b,c,d)
  orelse between(a,b,c)
  orelse between(a,b,d)
  orelse between(c,d,a)
  orelse between(c,d,b)


(* a polygon is specified by points in counterclockwise order
 * internally, this is represented as a doubly-linked list,
 * with a "distinguished point" as the head of the list.
 * thus a vertex is a point w/ adjacency info + some bookkeeping,
 * and a polygon is a reference to one of these vertices. *)
datatype vertex = Nil
		| Vertex of {prev : vertex ref, next : vertex ref,
			     coords : point, ear : bool ref}
type polygon = vertex ref;				

exception NilVertex
fun next Nil = raise NilVertex
  | next (Vertex v) = #next v
fun prev Nil = raise NilVertex
  | prev (Vertex v) = #prev v
fun coords Nil = raise NilVertex
  | coords (Vertex v) = #coords v
fun ear Nil = raise NilVertex
  | ear (Vertex v) = #ear v

(* insert a point p as the clockwise neighbor to the head of u *)
fun insertLeft (u : polygon, p : point) =
  case !u of
      Nil => let val left = ref Nil
		 val right = ref Nil
		 val new = Vertex {prev = left, next = right, coords = p, ear = ref false}
	     in (right := new; left := new; u := new) end
    | (Vertex v) =>
      let val left = #prev v
	  val new = Vertex {prev = ref(!left), next = ref(!u), coords = p, ear = ref false}
      in ((next (!left)) := new; left := new ) end

(* cut out the head of u, replacing it with its counterclockwise neighbor *)	  
fun excise (u : polygon) =
  case !u of
      Nil => raise NilVertex
    | Vertex {prev=left, next=right, coords=_, ear=_}
      => ((next (!left))  := !right;
	  (prev (!right)) := !left;
	  u := !right)

(* move the head counterclockwise *)	     
fun moveRight (u: polygon) = (u := !(next(!u)))

(* fold over vertices *)				 
fun foldV (f : vertex ref * 'a -> 'a) a0 (v : polygon)
  = let val u = ref (!v)
        val a = ref (f (u,a0))
    in (u := !(next(!u));
	while (!u <> !v) do (a := f(u,!a); u := !(next(!u)));
	!a) end
	
(* fold over edges, i.e. adjacent ccw pairs of vertices *)
fun foldE (f : vertex ref * vertex ref * 'a -> 'a) a0 (v : polygon)
  = let fun vf (u,a) = f (u,next(!u),a)
    in foldV vf a0 v end

fun triplet (v : vertex ref) =
  case !v of Nil => raise NilVertex
	  | (Vertex {next=r,prev=l,coords=_,ear=_}) => (l,v,r)
(* fold over triplets *)	
fun foldT (f : vertex ref * vertex ref * vertex ref * 'a -> 'a) a0 v
  = let fun tf (u,a) = let val (u0,_,u1) = triplet (u)
		       in f(u0,u,u1,a) end
    in foldV tf a0 v end

fun fromPoints (ps : point list) : polygon
  = let fun attach (p,u) = (insertLeft(u,p); u)
    in foldl attach (ref Nil) ps end	

fun toPoints (v : polygon)
  = rev (foldV (fn (u,ps) => (coords (!u))::ps) [] v)

(* compute twice the signed area of a polygon 
 * by computing the signed area of triangles of 
 * the form (head,u,v) where v is the ccw neighbor of u. 
 * note that this is a lot easier than computing a proper
 * triangulation. *)
fun areaPoly2 (v : polygon)
  = let	fun triArea (u : vertex ref, total) = 
	  total + area2(coords (!v), coords (!u), coords (!(next(!u))))
    in foldV triArea 0 v end

(* is b in the cone formed by the triplet at a *)	
fun inCone (a : vertex ref, b : vertex ref)
  = let val a0 = coords (!(prev(!a)))
	val a1 = coords (!(next(!a)))
	val a = coords (!a)
	val b = coords (!b)
    in if leftOn (a, a1, a0)
       then left(a, b, a0) andalso left(b, a, a1)
       else not (leftOn(a, b, a1) andalso leftOn(b, a, a0))
    end	
	

(* is ab a diagonal (interior or exterior) of the polygon v *)	
fun diagonalIE (v : polygon, a : vertex ref, b : vertex ref)
  = let fun veq u v = (!u = !v)
	fun inter (u,v,flag) =
	  flag andalso (veq u a orelse veq u b orelse veq v a orelse veq v b
			orelse not (intersection(coords (!a), coords (!b),
						 coords (!u), coords (!v))))
    in foldE inter true v end


fun diagonal (v: polygon, a : vertex ref, b : vertex ref)
  = inCone(a,b) andalso inCone(b,a) andalso diagonalIE(v,a,b)

(* an ear is a vertex whose triple forms a triangle
 * interior to the polygon. the triangulation algorithm
 * below keeps track of which vertices are ears, here 
 * we initialize the flag. *)
fun earInit (v : polygon) =
  let fun setEar (v0,v,v1,_) = ear(!v) := diagonal(v,v0,v1)
  in (foldT setEar () v; v) end

(* computes a triangulation of the polygon determined by 
 * n points in ccw order. the algorithm below is O(n^2) time. *)      
fun triangulate (ps : point list)
  = let val v = earInit(fromPoints ps)
	val n = (length ps)
	fun nextEar (u : vertex ref) =
	    if !(ear(!u)) then u else nextEar (next(!u))
	fun clipEars (n,edges) =
	  if n > 3
	  then let val u = nextEar v
		   val (u1,_,u3) = triplet u
		   val u0 = prev(!u1)
		   val u4 = next(!u3)
	       in  (ear(!u1) := diagonal(v,u0,u3);
		    ear(!u3) := diagonal(v,u1,u4);
		    excise(u);
		    clipEars(n-1,
			     (coords(!u1), coords(!u3))::edges))
	       end
	  else edges
    in clipEars (n,nil) end

(* useful functions for rendering polygons and triangulations *)	

fun wh (ps : point list) =
  let val SOME min = Int.minInt
      fun pairmax ((x,y),(a,b)) = (Int.max(x,a), Int.max(y,b))
  in foldr pairmax (min,min) ps end	
	
fun i2s i =
    if i < 0 then "-" ^ Int.toString (~i) else Int.toString i	
							    
fun polySVG (ps : point list) =
  let fun pointToString (x,y) = i2s x ^ "," ^ i2s y
      val coordString = foldr (fn (p,s) => (pointToString p)^" "^ s) ""
      val polyString = "<polygon points=\"" ^ (coordString ps)^"\" fill=\"none\" stroke=\"black\" />"
  in polyString end

fun segSVG ((x1,y1) : point, (x2,y2) : point) =
  "<line x1=\"" ^ i2s x1 ^ "\" y1=\"" ^ i2s y1 ^
  "\" x2=\"" ^ i2s x2 ^ "\" y2=\"" ^ i2s y2 ^
  "\" stroke=\"royalblue\" />"

fun svgWrap (w,h,s : string) =
  let val prefix = "<svg height=\"" ^ Int.toString h ^ "\" width=\"" ^ Int.toString w ^ "\">"
      val suffix = "</svg>"
  in prefix ^ "\n" ^ s ^ "\n" ^ suffix end
      
	
(* test cases *)
val square = [(0,0), (1,0), (1,1), (0,1)];
val oddQuad = [(0,0), (1,1), (2,0), (1,2)];
val bigSquare = [(0,0), (100,0), (100,100), (0,100)];
val testPoly = map (fn (x,y) => (30*x + 100,30*y + 100))
		   [(0,0), (10,7), (12,3),
		    (20,8), (13,17), (10,12),
		    (12,14), (14,9), (8,10),
		    (6,14), (10,15), (7,18),
		    (0,16), (1,13), (3,15),
		    (5,8), (~2,9), (5,5)]


		   
fun writePolySVG (ps : point list, fname : string)
  = let val os = TextIO.openOut fname
	val (width, height) = wh ps
    in (TextIO.output(os, svgWrap(width, height, polySVG ps));
	TextIO.closeOut os) end
		   

fun writeTriangulationSVG (ps : point list, fname : string) =
  let val es = triangulate(ps)
      val pstr = polySVG ps
      val estr = concat (map segSVG  es)
      val out = TextIO.openOut fname
      val (width,height) = wh ps
  in (TextIO.output(out, svgWrap(width, height, pstr ^ estr));
      TextIO.closeOut out) end
	
