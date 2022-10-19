# Trail

    signature TRAIL =
       sig
    
          type term
          type ebind
          
          (* When a mark to be rewound is already committed, Rewind is raised.
             When a mark to be rewound is obsolete (that is, an older mark has
             been rewound) the behavior is undefined but sound (that is: nothing
             committed will rewound, and tokens will be properly invalidated for
             whatever happens to get rewound).  To guard against this, keep all
             marks local.
          *)
    
          type mark
          exception Rewind
          val mark : unit -> mark
          val rewind : mark -> unit
          val commit : unit -> unit
          
          type token
          val merge : token -> token -> token
          val token : unit -> token
          val valid : token -> bool
          val always : token
    
       end
