CM.make "../ipp/sources.cm";
CM.make "../basis/basis.cm";
use "tags.sml";

fun go (_, args) = TagsCommandLine.main args ;

SMLofNJ.exportFn ("bin/istaritags-heapimg", go) ;
