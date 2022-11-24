
COQC = coqc
COQDEP = coqdep

UNITS = \
	Axioms \
	Candidate \
	Ceiling \
	Constructor \
	ContextHygiene \
	Defined \
	Defs \
	DefsEquiv \
	DeprecatedTactics \
	DerivedRules \
	Dots \
	Dynamic \
	Equality \
	Equivalence \
	Equivalences \
	Extend \
	ExtSpace \
	ExtendTruncate \
	Hygiene \
	Intensional \
	IntensionalNerect \
	Judgement \
	Lattice \
	MapTerm \
	Model \
	Morphism \
	MuIndExtract \
	Obligations \
	Ofe \
	Ordinal \
	Page \
	PageCode \
	PageType \
	Possible \
	PreSpacify \
	Promote \
	ProperClosed \
	ProperDownward \
	ProperEquiv \
	ProperFun \
	ProperLevel \
	ProperMono \
	Reduction \
	Relation \
	Rules \
	Semantics \
	SemanticsAll \
	SemanticsExist \
	SemanticsEqual \
	SemanticsFut \
	SemanticsEqtype \
	SemanticsGuard \
	SemanticsKnot \
	SemanticsKuniv \
	SemanticsMu \
	SemanticsPi \
	SemanticsPositive \
	SemanticsProperty \
	SemanticsQuotient \
	SemanticsSet \
	SemanticsSigma \
	SemanticsSimple \
	SemanticsSubtype \
	SemanticsUniv \
	SemanticsWtype \
	Sequence \
	Shut \
	Sigma \
	SimpSub \
	SoundAll \
	SoundEqtype \
	SoundEqual \
	SoundExist \
	SoundFut \
	SoundGuard \
	SoundHyp \
	SoundKuniv \
	SoundMisc \
	SoundMu \
	SoundRec \
	SoundPi \
	SoundPositive \
	SoundQuotient \
	SoundSet \
	SoundSigma \
	SoundSimple \
	SoundSubstitution \
	SoundSubtype \
	SoundStructural \
	SoundUtil \
	SoundUniv \
	SoundWtype \
	Soundness \
	Spaces \
	Spacify \
	Standard \
	Standardization \
	Subst \
	Subsumption \
	Syntax \
	System \
	Tactics \
	Truncate \
	Uniform \
	Urelsp \
	Validation \
	ValidationAcc \
	ValidationAll \
	ValidationPi \
	ValidationExist \
	ValidationFuture \
	ValidationLevel \
	ValidationMu \
	ValidationNat \
	ValidationQuotient \
	ValidationSigma \
	ValidationSimple \
	ValidationSum \
	ValidationUniv \
	ValidationUtil


SOURCES = $(foreach i, $(UNITS), $(i).v)
OBJS = $(foreach i, $(UNITS), $(i).vo)

.PHONY : all clean

all : $(OBJS)

%.vo : %.v
	$(COQC) -q -nois $<

clean :
	rm *.vo *.glob

depend : $(SOURCES) Makefile
	$(COQDEP) $(SOURCES) > depend

tags : $(SOURCES)
	coqtags $(SOURCES)

include depend
