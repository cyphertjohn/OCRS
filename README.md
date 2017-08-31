OCRS
====
The Operational Calculus Recurrence Solver (OCRS) is an ocaml library designed to symbolically solve linear recurrences.

## Classes of recurrences

OCRS is designed to solve the following classes of recurrences:

### Univariate Linear recurrences

These are recurrences of the form

* y_{n+1} = a * y_n + f(n), where f(n) is an expression involving polynomials and exponentials

Some examples of this type of recurrences are:

1. y_{n+1} = y_n + 1
2. y_{n+1} = y_n + n ^ 4 + n ^ 3
3. y_{n+1} = 2 * y_n
4. y_{n+1} = 3 * y_n + n ^ 2 * 2 ^ n

OCRS will give the following solutions to the above recurrences:

1. y_n = y_0 + 1
2. y_n = y_0 + (-1/30 * n) + (1/4 * n ^ 2) + (-1/6 * n ^ 3) + (-1/4 * n ^ 4) + (1/5 * n ^ 5)
3. y_n = y_0 * 2 ^ n
4. y_n = (-10 * 2 ^ n) + (10 * 3 ^ n) + (y_0 * 3 ^ n) + (-4 * 2 ^ n * n) + (-1 * 2 ^ n * n ^ 2)

### Divide and Conquer recurrences

These are recurrences of the form:

* y_n = a * y_{n/b} + p(n), where p(n) is a polynomial in n

Some examples of this type of recurrence are:

1. y_n = y_{n/2} + 1
2. y_n = 2 * y_{n/2} + n
3. y_n = 3 * y_{n/2} + n

OCRS will give the following solutions to the above recurrences:

1. y_n = y_1 + log2(n)
2. y_n = y_1 * n + n * log2(n)
3. y_n = -2 * n + 2 * n ^ (log2(3)) + y_1 * n ^ (log2(3))

### Matrix recurrences

OCRS able to solve what we call "matrix recurrences". These are recurrences of the form:

```
| x1_{n+1} |        | x1_n |   | f1(n) |
| x2_{n+1} |        | x2_n |   | f2(n) |
| x3_{n+1} |  = A * | x3_n | + | f3(n) |
|   ...    |        |  ... |   |  ...  |
| xk_{n+1} |        | xk_n |   | fk(n) |
```
where A is a k-by-k matrix with rational entries, and each fi(n) is an expression involving polynomials and exponentials.

An example of this type of recurrence is the following:

```
|x_{n + 1} | = |  1 1 | * | x_n | + | n | 
|y_{n + 1} |   | -2 4 |   | y_n |   | 1 |
```

which has the followign solution:
```
x_n == (-5/4 + 2 ^ n + (2 * x_0 * 2 ^ n) + (-1 * y_0 * 2 ^ n) + (1/4 * 3 ^ n) + (-1 * x_0 * 3 ^ n) + (y_0 * 3 ^ n) + (-3/2 * n))
y_n == (-3/2 + 2 ^ n + (2 * x_0 * 2 ^ n) + (-1 * y_0 * 2 ^ n) + (1/2 * 3 ^ n) + (-2 * x_0 * 3 ^ n) + (2 * y_0 * 3 ^ n) + (-1 * n))
```

There are two special situations that can occur with matrix recurrences:

#### A has non-rational eigenvalues
If A has non-rational eigenvalues (irrational or complex) then OCRS will be unable to return a solution to the reccurence in standard algebra. (To solve this problem OCRS would need to be able to factor arbitrary polynomials). However, OCRS will still have a unique internal representation for the recurrence solution. Thus, in this situation OCRS will return this "Implicitly intrepreted function" (IIF) as a unintrepreted function characterized by a cannonical string.

Consider the following example:
```
| x_{n + 1} |    |  1 1 |   | x_n |   | 0 |
| y_{n + 1} | == | -9 1 | * | y_n | + | 0 |
```
The matrix involved in this recurrence has eigenvalues 1+3i and 1-3i, which in general OCRS is not able to discern. Thus instead will return the following solution for x_n with an IIF:

```
x_n == (x_0 + (-9 * x_0 * f{(10 + (-2 * q) + q ^ 2) ^ -1}(n)) 
     + (-1 * y_0 * f{(10 + (-2 * q) + q ^ 2) ^ -1}(n)) 
     + (y_0 * f{(10 + (-2 * q) + q ^ 2) ^ -1}({n + 1})))
```
The IIFs in question are f{(10 + (-2 * q) + q ^ 2) ^ -1}(n), and f{(10 + (-2 * q) + q ^ 2) ^ -1}(n+1), where f{(10 + (-2 * q) + q ^ 2) ^ -1}(n+1) is the same function as the first just shifted by one.

#### A has eigenvalues of zero
In this situation the result requires a piecewise function or a shift operator to represent the solution. When solving a matrix recurrence OCRS has the ability to return a solution in either representation.

Building
====

OCRS uses gmp to as an internal representation for constants. Therefore, to use OCRS a install of gmp and bindings for ocaml are required.

OCRS uses the ocaml build tool oasis to assist in building. Note that it is not required to have oasis installed to use OCRS though. 

To re-generate setup.ml have oasis installed and use:
```
oasis setup
```

To build the project using setup.ml:
```
ocaml setup.ml -build
```

To install using setup.ml:
```
ocaml setup.ml -install
```

To generate documentation:
```
ocaml setup.ml -doc
```

### Installing with opam
While OCRS is not part of the default opam repository, there are appropriate files in the opam directory for the most current version of OCRS to be installed via a custom opam repository.

If you would like to install OCRS via this method copy the files in the opam directory to your custom repository.

Alternatively, the current version of OCRS is a part of the repository git://github.com/zkincaid/sv-opam.git.

This repository can be added to your opam with:
```
opam remote add sv git://github.com/zkincaid/sv-opam.git
```
Once your opam points to a repository with OCRS files it can be installed with:

```
opam install ocrs
```

Misc
====
OCRS is based on the operational calculus algebra created by Lothar Berg. For more information on the theory of OCRS consult the papers directory.

* Currently the only paper in that directory is a write-up for a class project that only covers how to solve the first class of recurrences listed here. There is no current write-up for solving the other two classes of recurrences.


The test.ml file in the examples directory gives some example usages of OCRS. To learn the usage of OCRS I recommend looking there as well as looking at the documentation for the modules Ocrs and Type_def.
