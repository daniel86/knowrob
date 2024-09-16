Terms {#terms}
============

Terms are central data structures in KnowRob. They are used to recursively
form complex formula that can be queried and reasoned about. The following
sections describe the most important terms and their usage.

The base class for all terms is `Term`. It provides basic functionality for
manipulating terms, such as querying the type of term, checking for equality,
and printing terms in a human-readable format.
Its direct subclasses are `Atomic`, `Variable`, and `Function`.
A `Function` is a compound term that consists of a functor and a list of
arguments. The functor is an atom (atomic), and arguments are terms.
A `Variable` is a term that can be bound to a value. However, in KnowRob
variables are immutable, i.e., a variable object cannot be changed, when
it is bound to a value, a new object is created.

Here are some example expressions that are valid string forms of a term
(as supported by `QueryParser`):

| Expression        | Term type |
|-------------------|-----------|
| `1`               | Double    |
| `x`               | Atom      |
| `'1'`             | Atom      |
| `"x"`             | String    |
| `owl:x`           | IRIAtom   |
| `45^^xsd:integer` | Integer   |
| `p(x)`            | Function  |
| `?x`              | Variable  |
| `X`               | Variable  |


### Atomic terms

The `Atomic` class is the base class for all atomic terms, i.e., terms that
cannot be further decomposed. The subclasses of `Atomic` are `XSDAtomic`, and
`Atom`. `XSDAtomic` corresponds to XML Schema Datatypes, such as `xsd:integer`,
`xsd:float`, `xsd:string`, etc. `Atom` is a subclass of `XSDAtomic` that
represents an atom, i.e., a constant symbol.
Atoms are allocated in a global atom table, which ensures that there is only
one object for each atom. The `Atom` class has as subclasses `IRIAtom` and
`Blank` used to represent IRIs and blank nodes in RDF graphs.

### Atom vs. String

KnowRob employs a distinction between `Atom` and `String`. An `Atom` is a constant symbol that is used to represent
names of objects, relations, etc. in the knowledge base. A `String` is a sequence of
characters that is used to represent text. The `String` class is a subclass of
`XSDAtomic` and is used to represent strings in XML Schema Datatypes.
Furthermore, in input strings, atoms are enclosed in single quotes, while strings
are enclosed in double quotes.
Further note that there are two different classes for strings: `String` and `StringView`.
The former creates a copy of the string, while the latter only stores a reference to
the string to avoid unnecessary copying of strings (*i.e. care must be taken when using `StringView`*).

### Bindings

Another central notion around terms are *bindings*. A `Binding` is a mapping
from variables to terms. Such a binding can be used to substitute variables
in a term with their corresponding values. The `Bindings` class provides
functionality to create, query, and manipulate bindings. Bindings are usually
created when querying the knowledge base. A `Unifier` is a special kind of
binding that can be used to unify two terms, i.e., to find a substitution
that makes two terms syntactically equal.
