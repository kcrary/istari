CM.make "../ipp/sources.cm";
use "tags.sml";

fun go (_, args) = TagsCommandLine.main args ;

SMLofNJ.exportFn ("bin/istaritags-heapimg", go) ;
