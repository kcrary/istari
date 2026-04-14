
COQC = coqc
COQDEP = coqdep

UNITS = \
	Absentia \
	Approximation \
	Axioms \
	Candidate \
	Ceiling \
	Compactness \
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
	Native \
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
	SemanticsConstfn \
	SemanticsExist \
	SemanticsEqual \
	SemanticsFut \
	SemanticsEqtype \
	SemanticsGuard \
	SemanticsKnot \
	SemanticsKind \
	SemanticsMu \
	SemanticsNative \
	SemanticsPartial \
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
	SoundAdmiss \
	SoundAll \
	SoundConstfn \
	SoundEqtype \
	SoundEqual \
	SoundExist \
	SoundFut \
	SoundGuard \
	SoundHyp \
	SoundKind \
	SoundMisc \
	SoundMu \
	SoundNative \
	SoundPartial \
	SoundPartialUtil \
	SoundRec \
	SoundPartial \
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
	SoundSwap \
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
	Unshut \
	Urelsp \
	Validation \
	ValidationAcc \
	ValidationAll \
	ValidationCompat \
	ValidationEqtp \
	ValidationEqual \
	ValidationExist \
	ValidationForallfut \
	ValidationFuture \
	ValidationGuard \
	ValidationIstp \
	ValidationLevel \
	ValidationMisc \
	ValidationMu \
	ValidationNat \
	ValidationNative \
	ValidationOf \
	ValidationParam \
	ValidationPartial \
	ValidationPi \
	ValidationQuotient \
	ValidationRec \
	ValidationSequal \
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
