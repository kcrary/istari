# Modules

The Istari library provides a lightweight module system to avoid
cluttering the namespace.  Constants belonging to a module are
accessed by a compound name (*e.g.,* `Nat.plus`).

- `beginModule "[name M]"`

  Open a module named `M`.  Subsequent definitions, etc. will be part
  of `M`.

- `endModule ()`

  Close the current module.

- `openModule /[compound name M]/`

  Make the contents of `M` available without using a compound name.
  For example, opening `Nat` makes `Nat.plus` accessible by `plus`.

- `alias /[new name]/ /[constant]/`

  Create an alias to an existing constant.  The name will not become
  part of the current module.

- `aliasExport /[new name]/ /[constant]/`

  Create an alias to an existing constant.  The name *will* become
  part of the current module.

- `aliasModule /[new name]/ /[compound module name]/`

  Create an alias to an existing module.  The name will not become
  part of the current module.

- `Namespace.currentModule ()`

  Print the current module's name.
