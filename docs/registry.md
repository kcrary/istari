# Registry

The registry provides a mechanism for including certain Istari data
structures in an Istari file.  Currently terms and reductions can be
registered.

Registry items are cast to a common type (`item`) and then given a
name in the registry.  When an item is registered, the current module
name is attached to the front of its name.  The item is recovered by
reading it from the registry by name, and casting it back to the
appropriate type.

For example, the `notb_tru` reduction (with type
`Reduction.ureduction2`) is obtained by:

    val notb_tru = Registry.toUreduction2 (Registry.read (parseLongident /Bool.notb_tru/))


The interface for the registry is:

    signature REGISTRY =
       sig
    
          type item
    
          exception Registry of string
    
          val write : Symbol.symbol -> item -> unit
          val read : Symbol.symbol list -> item
    
          val toTerm : item -> Term.term
          val toReduction : item -> Reduction.reduction
          val toUreduction1 : item -> Reduction.ureduction1
          val toUreduction2 : item -> Reduction.ureduction2
    
          val fromTerm : Term.term -> item
          val fromReduction : Reduction.reduction -> item
          val fromUreduction1 : Reduction.ureduction1 -> item
          val fromUreduction2 : Reduction.ureduction2 -> item
    
       end

The `Registry` exception is raised when an item is not found, or when a cast fails.
