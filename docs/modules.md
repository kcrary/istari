# Modules

The Istari library provides a lightweight module system to avoid
cluttering the namespace.  Constants belonging to a module are
accessed by a compound name (*e.g.,* `Nat.plus`).

- `Namespace.beginModule "[name M]"`

  Open a module named `M`.  Subsequent definitions, etc. will be part
  of `M`.

- `Namespace.endModule ()`

  Close the current module.

- `Namespace.openModule (parseLongident /[compound name M]/)`

  Make the contents of `M` available without using a compound name.
  For example, opening `Nat` makes `Nat.plus` accessible by `plus`.

- `Namespace.alias (parseConstant /[constant]/)`

  Make the constant part of the current module.

- `Namespace.currentModule ()`

  Print the current module's name.

