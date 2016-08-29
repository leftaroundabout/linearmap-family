This project has two goals:

### To give Haskell a competitive, _native_ linear algebra library

That is, a library that supports:

1. Basic vector operations ✓
2. Efficient linear maps ✓
3. Solving linear equations
  1. Inversion of finite-dimensional, linear isomorphisms (full-rank matrices) ✓
  2. Least-squares solution to under/overdetermined problems (?)
  3. Fast iterative methods (for large sparse systems, e.g. conjugate gradient) ✗
4. Eigenvalue problems ✓
5. Singular value decomposition ✗

At the moment, the only Haskell libraries that offer all of that appear to be
[hmatrix](http://hackage.haskell.org/package/hmatrix) and [eigen](http://hackage.haskell.org/package/eigen),
which use bindings to the [GSL](https://www.gnu.org/software/gsl/) (C)
and [Eigen](http://eigen.tuxfamily.org/index.php?title=Main_Page) (C++) libraries.

- Eigen is a great project that uses the C++ template system for both an elegant interface and nice optimisations.
  However, this interface doesn't really translate that nicely over to Haskell. The C interface layer necessary
  forgets much of the template niceties.
- GSL is extremely comprehensive and well-suited for binding to other languages, in particular dynamic languages.
  However, it's a bit of a messy _big collection of all kind of algorithms_, and not exactly the fastest library,
  which adds to the general overhead of calling to external code with C-marshalled memory.

### To get rid of those pesky matrices

Linear algebra isn't really about matrices. Vectors aren't _really_ arrays of numbers.

What LA is really about are _points in vector spaces_, and ultimately geometric relations between them.
And many interesting spaces aren't even finite-dimensional.

Regardless of whether matrices are used for the internal operations – and in fact, it's not so clear if
this is always a good idea! – matrices shouldn't dominate the API of a linear algebra library.
Haskell has managed to bring a lot innovation to the world of programming languages.
It can nicely work with infinite, lazy data structures.
Hopefully it can also make a bit of a revolution in the field of linear algebra!
