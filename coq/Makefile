
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
	LevelLemmas \
	MapTerm \
	Model \
	Morphism \
	MuIndExtract \
	NatLemmas \
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
	SemanticsKind \
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
	SoundKind \
	SoundMisc \
	SoundMu \
	SoundRec \
	SoundPi \
	SoundPositive \
	SoundQuotient \
	SoundSequal \
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
	SumLemmas \
	Syntax \
	System \
	Tactics \
	Truncate \
	Uniform \
	Urelsp \
	Validation \
	ValidationAcc \
	ValidationAll \
	ValidationCompat \
	ValidationEqtp \
	ValidationEqual \
	ValidationExist \
	ValidationFuture \
	ValidationIstp \
	ValidationLevel \
	ValidationMisc \
	ValidationMu \
	ValidationNat \
	ValidationOf \
	ValidationPi \
	ValidationQuotient \
	ValidationRec \
	ValidationSet \
	ValidationSigma \
	ValidationSimple \
	ValidationSquash \
	ValidationSubtype \
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
