# Quadratic-Time Triangulation in SML

This is a fairly straightforward SML implementation of the polygon triangulation algorithm given in Chapter 1 of O'Rourke's "Computational Geometry in C". Basically, it can take a list of (x,y) coordinates, interpreted as specifying the vertices of a polygon in clockwise order, and output a list of pairs of points, corresponding to the line segments in a triangulation. There's also some helper code in there, to generate SVG images.

Basically, given something arbitrarily wonky, like this: 
![test polygon](https://cdn.rawgit.com/kilimanjaro/sml-triangulate/9aec0bd/testPoly.svg)

it can compute a list of edges so that you get something like this: 
![triangulated test polygon](https://cdn.rawgit.com/kilimanjaro/sml-triangulate/9aec0bd/testPolyTriangulated.svg)

## Remark
The algorithm works by successively clipping ears from the polygon, where an ear is a triangle formed by three adjacent vertices that could be included in a valid triangulation. There are faster algorithms, but this method is particularly simple. The implementation is very much stateful -- lots of references thrown around, etc.
