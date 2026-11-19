# Full statements for the étale-premises audit

Evidence for [`../etale-premises-sheaf-libraries-audit.md`](../etale-premises-sheaf-libraries-audit.md),
Sections 2, 4 and 5 (Task 7360, items 1–3). Worker 22 prepared it on 17 November 2026
from the pinned sources. Worker 19 added Sections C.5–C.9 on 18 November 2026, and
Sections B.7–B.8 and C.10–C.11 after the fifth review, Sections B.9–B.11 and C.12
after the sixth review, and Sections A.5 and B.12 after the seventh review, by the same method. It is an unreviewed development record. It is not a Library
statement and does not accept any external declaration.

## Conventions

- Every code block is copied verbatim from the source file named above it, with the
  line numbers given there. Where one block shows several line ranges of the same file,
  the ranges are separated by a line `-- ⋯`, which is not in the source.
- Before each declaration, its block reproduces the commands still in scope at that
  line: `namespace`, `section`, `open`, `universe`, `variable`, `include`,
  `attribute [local instance]`, and the `local instance` declarations of the section
  where they matter. Lean adds to a theorem's type the section variables that its
  statement mentions, the instance binders on them, and the variables named by
  `include`. For a definition it also adds the variables that its body uses.
- Sources: Library commit `fcb85a7ef43356fec01e6ccf1605f08568c08cb0` (paths from the
  Library root; Section A.5 from commit `f050c0b1b525624bc32c1e7c25a8d2841bb2d4e0`); AxiomMath/Stacks at `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
  registered literature `axiommath-stacks-c496df0`; FAG
  (formal-arithmetic-geometry/weil-conjectures) at
  `a25955cde4f85f67bef3149a6efc3efe20c22132`, registered literature
  `formal-arithmetic-geometry-weil-conjectures-a25955c`.
- Headings give full declaration names, as they resolve from the `namespace` lines.

## A. The Library's premises and the definitions they use

### A.1 General premises

`Langlands.Cohomology.EtaleGaloisSmooth.GaloisCohomologySmoothStatement`:

`Langlands/Cohomology/EtaleGaloisSmooth/Statement.lean`, lines 18–35:

```lean
namespace Langlands.Cohomology.EtaleGaloisSmooth

open AlgebraicGeometry Langlands.Geometry.EtaleGaloisAction

universe u

/-- For an algebraic field extension `L / K` and a quasi-compact
quasi-separated `f : X ⟶ Spec K`, the action of `L ≃ₐ[K] L`, with its Krull
topology, on every étale cohomology module of `X ×_{Spec K} Spec L` with
constant coefficients is smooth. -/
def GaloisCohomologySmoothStatement (K : Type u) [Field K] (L : Type u) [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [QuasiCompact f] [QuasiSeparated f]
    (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) (n : ℕ),
    Langlands.IsSmooth (galoisCohomologyRep (L := L) f R M n).ρ

end Langlands.Cohomology.EtaleGaloisSmooth
```

`Langlands.Cohomology.EtaleGaloisGoodReduction.GaloisCohomologyGoodReductionStatement`:

`Langlands/Cohomology/EtaleGaloisGoodReduction/Statement.lean`, lines 16–37:

```lean
namespace Langlands.Cohomology.EtaleGaloisGoodReduction

open AlgebraicGeometry Langlands.Geometry.EtaleGaloisAction Langlands.Shimura

universe u

/-- For a number field `K`, a smooth proper morphism `f : X ⟶ Spec K` and a commutative ring `R`,
there is a finite set `S` of finite places of `K` such that for every finite `R`-module `M`, every
degree `n` and every finite place `v ∉ S` at which the order of `M` is a unit, the action of the
absolute Galois group of `K` on the degree `n` étale cohomology of `X ×_{Spec K} Spec K̄` with
constant coefficients `M` is unramified at `v`. -/
def GaloisCohomologyGoodReductionStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IsProper f]
    (R : Type u) [CommRing R] : Prop :=
  ∃ S : Set (Global.FinitePlace K), S.Finite ∧
    ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ) (v : Global.FinitePlace K), v ∉ S →
      ((Nat.card M : NumberField.RingOfIntegers K) ∉ v.asIdeal) →
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))

end Langlands.Cohomology.EtaleGaloisGoodReduction
```

`Langlands.Cohomology.EtaleGaloisUnramified.GaloisCohomologyUnramifiedStatement`:

`Langlands/Cohomology/EtaleGaloisUnramified/Statement.lean`, lines 15–34:

```lean
namespace Langlands.Cohomology.EtaleGaloisUnramified

open AlgebraicGeometry Langlands.Geometry.EtaleGaloisAction Langlands.Shimura

universe u

/-- For a number field `K`, a morphism of finite type `f : X ⟶ Spec K` and a commutative ring
`R`: for every finite `R`-module `M` and every degree `n`, the action of the absolute Galois group
of `K` on the degree `n` étale cohomology of `X ×_{Spec K} Spec K̄` with constant coefficients
`M` is unramified at every finite place of `K` outside some finite set. -/
def GaloisCohomologyUnramifiedStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [QuasiCompact f] (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ),
    ∃ S : Set (Global.FinitePlace K), S.Finite ∧ ∀ v ∉ S,
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))

end Langlands.Cohomology.EtaleGaloisUnramified
```

### A.2 Harris premises at one level

`Langlands.Cohomology.HarrisCMCohomology.HarrisCMCohomologyFiniteStatement`,
`…HarrisCMGaloisCohomologySmoothStatement` and `…HarrisCMCohomologyStatements`, with the
whole variable block:

`Langlands/Cohomology/HarrisCMCohomology/Statement.lean`, lines 20–124:

```lean
noncomputable section

universe wS wR

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMCohomology

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura Langlands.Shimura.PEL
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "Rcoeff" => HarrisCoefficientIntegers K p

/-- Every étale cohomology module of every stage of the original geometric
CM torsion coefficient system on `X_U ×_{Spec F} Spec F̄` is finite. -/
def HarrisCMCohomologyFiniteStatement : Prop :=
  ∀ (degree : ℕ) (r : ℕᵒᵖ),
    Finite ((cmHarrisGeometricCoefficientCohomologySystem D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid degree).obj r)

variable [HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

/-- The constructed action of `F̄ ≃ₐ[F] F̄`, with its Krull topology, on every
étale cohomology module of every stage of the original geometric CM torsion
coefficient system on `X_U ×_{Spec F} Spec F̄` is smooth. -/
def HarrisCMGaloisCohomologySmoothStatement : Prop :=
  ∀ (degree : ℕ) (r : ℕᵒᵖ),
    Langlands.IsSmooth ((Rep.ActionToRep Rcoeff Galois).obj
      ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid degree).obj r)).ρ

/-- Both statements of this module: finiteness of every geometric CM torsion
cohomology module and smoothness of the constructed Galois action on it. -/
def HarrisCMCohomologyStatements : Prop :=
  HarrisCMCohomologyFiniteStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid ∧
    HarrisCMGaloisCohomologySmoothStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

end Langlands.Cohomology.HarrisCMCohomology
```

`Langlands.Cohomology.HarrisCMCohomologyUnramified.HarrisCMCohomologyUnramifiedStatement`.
Lines 20–83 of this file are identical to lines 20–83 of
`HarrisCMCohomology/Statement.lean` above, except line 32 (the namespace). The rest:

`Langlands/Cohomology/HarrisCMCohomologyUnramified/Statement.lean`, lines 32, 84–106:

```lean
namespace Langlands.Cohomology.HarrisCMCohomologyUnramified
-- ⋯
local notation "Rcoeff" => HarrisCoefficientIntegers K p

variable [HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

/-- There is a finite set `S` of finite places of `F` such that for every degree, every stage
of the original geometric CM torsion coefficient system on `X_U ×_{Spec F} Spec F̄` and every
finite place `w ∉ S`, the constructed action of `F̄ ≃ₐ[F] F̄` on the étale cohomology module is
unramified at `w`. The set `S` does not depend on the degree or the stage. -/
def HarrisCMCohomologyUnramifiedStatement : Prop :=
  ∃ S : Set (Global.FinitePlace F), S.Finite ∧
    ∀ (degree : ℕ) (r : ℕᵒᵖ) (w : Global.FinitePlace F), w ∉ S →
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{0} Rcoeff) w
        ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
          existence geometry hRigid degree).obj r)

end Langlands.Cohomology.HarrisCMCohomologyUnramified
```

All universe levels of the geometric objects are 0: `E F A L K W : Type`, the schemes of
the tower are in `Scheme.{0}`, and the cohomology is in `ModuleCat.{0} Rcoeff`, where
`Rcoeff = HarrisCoefficientIntegers K p : Type`. Only the derived-category instances
carry free universes, `wS` and `wR`.

### A.3 Harris premises over the level tower

`Langlands.Cohomology.HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement`, with
the whole variable block:

`Langlands/Cohomology/HarrisCMLevelGaloisSmooth/Statement.lean`, lines 17–91:

```lean
noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMLevelGaloisSmooth

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura Langlands.Shimura.PEL
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry
open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})
  (q : CMRepresentabilityStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})
  (R : Type) [CommRing R]

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)

/-- For every degree `d` and every sheaf `M` of `R`-modules on the small étale
site of `Spec F`, every class in the Library's colimit over all small CM levels of
`H^d(X_U ×_{Spec F} Spec F̄, M)` is fixed by an open subgroup of `F̄ ≃ₐ[F] F̄`,
with its Krull topology, under the constructed Galois action. -/
def HarrisCMLevelGaloisSmoothStatement : Prop :=
  ∀ (d : ℕ) (M : EtaleDerivedSections.ModuleSheaf (Spec (CommRingCat.of F)) R)
    (x : ((cmSmallLevelGaloisCohomologyFunctor D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry
      hRigid criterion R d).obj M).V),
    ∃ V : OpenSubgroup Galois, ∀ σ ∈ V,
      SmoothRep.hom (((cmSmallLevelGaloisCohomologyFunctor D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry
        hRigid criterion R d).obj M).ρ σ) x = x

end Langlands.Cohomology.HarrisCMLevelGaloisSmooth
```

`Langlands.Cohomology.HarrisCMPrimeToGaloisSmooth.HarrisCMPrimeToGaloisSmoothStatement`.
Lines 17–72 of this file are identical to lines 17–72 of
`HarrisCMLevelGaloisSmooth/Statement.lean` above, except line 27 (the namespace). The
rest:

`Langlands/Cohomology/HarrisCMPrimeToGaloisSmooth/Statement.lean`, lines 27, 73–93:

```lean
namespace Langlands.Cohomology.HarrisCMPrimeToGaloisSmooth
-- ⋯
local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q

/-- For every `m ≠ 0`, every level `K₀` at the places dividing `m`, every degree `d` and every
sheaf `M` of `R`-modules on the small étale site of `Spec F`, every class in the Library's
colimit, over the prime-to-`m` levels `K'` with `e⁻¹ (K₀ × K')` sufficiently small, of
`H^d(X_{e⁻¹ (K₀ × K')} ×_{Spec F} Spec F̄, M)` is fixed by an open subgroup of `F̄ ≃ₐ[F] F̄`,
with its Krull topology, under the constructed Galois action. Here `e` is the splitting
`cmPrimeToSplit D m hm`. -/
def HarrisCMPrimeToGaloisSmoothStatement : Prop :=
  ∀ (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
    (d : ℕ) (M : EtaleDerivedSections.ModuleSheaf (Spec (CommRingCat.of F)) R)
    (x : ((primeToGaloisCohomologyFunctor m hm K₀ existence geometry hRigid criterion R
      d).obj M).V),
    ∃ V : OpenSubgroup Galois, ∀ σ ∈ V,
      SmoothRep.hom (((primeToGaloisCohomologyFunctor m hm K₀ existence geometry hRigid
        criterion R d).obj M).ρ σ) x = x

end Langlands.Cohomology.HarrisCMPrimeToGaloisSmooth
```

Here the coefficient ring is any `R : Type`, and `M` is any sheaf of `R`-modules on the
small étale site of `Spec F`: there is no finiteness or torsion condition.

### A.4 Definitions used by the premises

Smoothness of a representation (`Langlands.IsSmooth`):

`Langlands/Representation/Smooth/Definitions.lean`, lines 14–19, 26–34:

```lean
namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]
-- ⋯
variable [TopologicalSpace G]

/-- A vector is smooth if an open subgroup fixes it. -/
def IsSmoothVector (ρ : Representation R G V) (v : V) : Prop :=
  ∃ K : OpenSubgroup G, v ∈ fixedVectors ρ K.toSubgroup

/-- A representation is smooth if all its vectors are smooth. -/
def IsSmooth (ρ : Representation R G V) : Prop :=
  ∀ v : V, IsSmoothVector ρ v
```

Unramified at a finite place (`Langlands.Shimura.DecompositionGroupAction.IsUnramifiedAt`):

`Langlands/Shimura/DecompositionGroupAction.lean`, lines 17, 21, 23, 25, 135, 137, 226–235:

```lean
universe u v w uK uE uH uG
-- ⋯
namespace Langlands.Shimura.DecompositionGroupAction
-- ⋯
open CategoryTheory Langlands.GaloisRepresentation
-- ⋯
variable (V : Type u) [Category.{v} V]
-- ⋯
section FinitePlace
-- ⋯
variable {K : Type uK} [Field K] [NumberField K] (v : Global.FinitePlace K)
-- ⋯
/-- An action is unramified at `v` along `ι` if the actual inertia subgroup of the completion,
the kernel of its residue action, acts trivially after restriction along `ι`. -/
def IsUnramifiedAlong (M : Action V (Field.absoluteGaloisGroup K))
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) : Prop :=
  ∀ i : localInertia v, ((atFinitePlace V v ι).obj M).ρ i.val = 𝟙 M.V

/-- An action is unramified at `v` if it is unramified along Mathlib's chosen closure
embedding. -/
def IsUnramifiedAt (M : Action V (Field.absoluteGaloisGroup K)) : Prop :=
  IsUnramifiedAlong V v M (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
```

The Galois action on constant-coefficient cohomology
(`Langlands.Geometry.EtaleGaloisAction.galoisCohomologyRep` and
`Langlands.Geometry.EtaleCohomologyAction.constantCohomologyRep`). `galoisAut f σ` is the
automorphism `baseChangeAut f σ` of `X ×_{Spec K} Spec L`, induced by `Spec σ`:

`Langlands/Geometry/EtaleGaloisAction.lean`, lines 14–21, 26, 76–77, 87–92:

```lean
namespace Langlands.Geometry.EtaleGaloisAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

variable (K : Type u) [CommRing K] (L : Type u) [CommRing L] [Algebra K L]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
-- ⋯
variable {K L}
-- ⋯
def galoisAut : (L ≃ₐ[K] L) →* (Aut (baseChange K L f))ᵐᵒᵖ where
  toFun σ := MulOpposite.op (baseChangeAut f σ)
-- ⋯
variable (R : Type u) [CommRing R]

/-- The action of `L ≃ₐ[K] L` on degree `n` étale cohomology of the base change
`X ×_{Spec K} Spec L` with constant coefficients `M`. -/
def galoisCohomologyRep (M : ModuleCat.{u} R) (n : ℕ) : Rep.{u} R (L ≃ₐ[K] L) :=
  EtaleCohomologyAction.constantCohomologyRep R (galoisAut f) M n
```

`Langlands/Geometry/EtaleConstantCohomology.lean`, lines 15–26, 78–81:

```lean
namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry.EtaleAutomorphism Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)
-- ⋯
def constantCohomologyRep (M : ModuleCat.{u} R) (n : ℕ) : Rep.{u} R G :=
  (Rep.ActionToRep R G).obj
    (TranslationAction.coCohomologyAction (sectionsTop R) (constantCoequivariant R ρ M)
      (injectiveResolution (constant R M)) n)
```

The Harris Galois action at one level
(`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.cmHarrisGeometricGaloisCohomologyAction`)
and its underlying module, the cohomology of the geometric coefficient system:

`Langlands/Shimura/PEL/HarrisTaylorCMGeometricGaloisCohomology.lean`, lines 131–135, 163–167:

```lean
/-- Every original ordinary-cohomology inverse system carries the
constructed Galois actions and equivariant reductions. -/
def cmHarrisGeometricGaloisCohomologyAction (degree : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat Rcoeff) Galois :=
  (galoisCoefficients).cohomologyAction degree
-- ⋯
@[simp] theorem cmHarrisGeometricGaloisCohomologyAction_obj_V
    (degree : ℕ) (r : ℕᵒᵖ) :
    (((cohomologyAction) degree).obj r).V =
      (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) Rcoeff degree).obj
        ((geometricSystem).obj r) := rfl
```

The level-tower action used by `HarrisCMLevelGaloisSmoothStatement`
(`cmSmallLevelGaloisAut`, `cmSmallLevelGaloisCohomologyFunctor` and the description of
the action on a class coming from one level, `cmSmallLevelGaloisCohomology_ρ_ι_apply`;
namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`):

`Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelGaloisCoefficients.lean`, lines 116–126, 260–269, 299–315:

```lean
/-- Galois automorphisms of the actual geometric CM tower, via the constructed comparison. -/
def cmSmallLevelGaloisAut (σ : Gamma) : Aut geometricSchemes :=
  (baseChangeIso).symm ≪≫
    RestrictedLevelTowerGalois.towerGaloisAut arithmeticStructure σ ≪≫ baseChangeIso

local notation "galoisAut" => cmSmallLevelGaloisAut D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

/-- At each actual CM level the Galois map acts on the algebraic-closure factor. -/
@[simp] theorem cmSmallLevelGaloisAut_hom_app (σ : Gamma) (U : SmallCMLevel D) :
    (galoisAut σ).hom.app U =
      EtaleGaloisAction.baseChangeMap ((arithmeticStructure).app U) σ := by
-- ⋯
/-- The commuting Galois action on the actual geometric CM cohomology, natural in
arithmetic base sheaves. The Galois group here has its algebraic group structure. -/
def cmSmallLevelGaloisCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤ Action (SmoothRep.{0, 0, 0} R G) Gamma := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.automorphismActionFunctor
    R arithmeticGeometricStructure selfTrivial galoisAction galoisOver d
-- ⋯
/-- At a level representative, Galois acts by the ordinary cohomological pullback and
the constructed projection-coefficient comparison at that same actual CM level. -/
theorem cmSmallLevelGaloisCohomology_ρ_ι_apply (d : ℕ) (M : ModuleSheaf base R)
    (σ : Gamma) (U : SmallCMLevel D)
    (x : (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) R d).obj
      ((EtaleInverseImage.inverseImage ((arithmeticGeometricStructure).app U) R).obj M)) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    SmoothRep.hom (((galoisCohomologyFunctor d).obj M).ρ σ)
        ((RestrictedLevelColimit.ι ((arithmeticCoefficients M).cohomology d) U).hom x) =
      (RestrictedLevelColimit.ι ((arithmeticCoefficients M).cohomology d) U).hom
        ((LevelTowerCohomology.projectionCohomologyMap R
          ((arithmeticGeometricStructure).app U) ((arithmeticGeometricStructure).app U)
          ((galoisAction σ).unop.hom.app U) (NatTrans.congr_app (galoisOver σ) U)
          d M).hom x) := by
```

Every class of the level colimit comes from one level
(`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.cmSmallLevelCohomology_exists_level_class`;
its section variables, lines 60–88 of the file, are the level block of A.3 with
`R : Type` and `criterion`):

`Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelCohomology.lean`, lines 236–245:

```lean
/-- Provided a small CM level exists, every cohomology class in the shrinking
colimit is represented at one actual small level. -/
theorem cmSmallLevelCohomology_exists_level_class [Nonempty (SmallCMLevel D)]
    (coeff : coefficients) (d : ℕ)
    (x : (colimit (cmSmallLevelCohomologyDiagram D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q
      existence geometry hRigid criterion R coeff d) : ModuleCat.{0} R)) :
    ∃ (U : SmallCMLevel D) (y : (levelCohomology coeff d).obj (op U)),
      (RestrictedLevelColimit.ι (levelCohomology coeff d) U).hom y = x := by
```

The level-`U` operator in `cmSmallLevelGaloisCohomology_ρ_ι_apply` is the pullback along
an étale map over the base, followed by the comparison of the inverse images of `M`
(`Langlands.Shimura.LevelTowerCohomology.projectionCohomologyMap`):

`Langlands/Shimura/LevelTowerCanonicalCoefficients.lean`, lines 7, 9, 11, 13–15, 21, 23, 101–106:

```lean
noncomputable section
-- ⋯
universe u v
-- ⋯
namespace Langlands.Shimura.LevelTowerCohomology
-- ⋯
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
-- ⋯
section Projection
-- ⋯
variable (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}
-- ⋯
/-- Pullback of degree `n` cohomology along an étale map `f`, with coefficients compared
along a commuting triangle `f ≫ q = r`. -/
def projectionCohomologyMap (q : Z ⟶ X) (r : Y ⟶ X) (f : Y ⟶ Z) [Etale f] (h : f ≫ q = r)
    (n : ℕ) (M : ModuleSheaf X R) :
    (EtaleDerivedSections.cohomology Z R n).obj ((inverseImage q R).obj M) ⟶
      (EtaleDerivedSections.cohomology Y R n).obj ((inverseImage r R).obj M) :=
```

### A.5 The Library's number-field spreading theorems (inputs to bridges B3 and F4)

These blocks are copied from Library commit `f050c0b1b525624bc32c1e7c25a8d2841bb2d4e0`, the base of this note. Every file except `NumberFieldAlmostAllLocalPoints.lean` is byte-identical at `fcb85a7e`. That file is not present at `fcb85a7e`.

Levels: finite sets of finite places containing a given one (`Langlands.Global.AdelicLevelIndexAbove`). The ring `(T : Set (FinitePlace K)).integer K` is Mathlib's ring of elements of `K` that are integral at every finite place outside `T`:

`Langlands/Global/AdelicFixedModelSystem.lean`, lines 9, 11–12, 14, 17–20:

```lean
universe u
-- ⋯
open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯

/-- Finite sets containing the fixed initial set, ordered by inclusion. -/
abbrev AdelicLevelIndexAbove {ι : Type u} (S : Finset ι) :=
  {T : Finset ι // S ⊆ T}
```

The generic fibre of a model, the inclusion of one ring of `T`-integers into a larger one, and the base change of a model along it (`Langlands.Global.numberFieldModelGenericFiber`, `Langlands.Global.numberFieldSIntegersMap`, `Langlands.Global.numberFieldLevelModelBaseChange`):

`Langlands/Global/AdelicGenericFiberPoints.lean`, lines 9, 11–12, 14, 128, 130–131, 133–138:

```lean
universe u
-- ⋯
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
section NumberField
-- ⋯
variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))
-- ⋯
/-- The actual pullback along the original number-field integer-subring inclusion. -/
def numberFieldModelGenericFiber
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    Over (Spec (CommRingCat.of K)) :=
  (Over.pullback
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).obj X
```
`Langlands/Global/AdelicLevelModelTransition.lean`, lines 9, 11–12, 14, 92, 94–95, 97–100, 113–117:

```lean
universe u
-- ⋯
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
section NumberField
-- ⋯
variable (K : Type u) [Field K] [NumberField K]
variable {S T : Finset (FinitePlace K)} (hST : S ⊆ T)
-- ⋯
/-- The literal inclusion of Mathlib's original number-field S-integer rings. -/
def numberFieldSIntegersMap :
    (S : Set (FinitePlace K)).integer K →+* (T : Set (FinitePlace K)).integer K :=
  Subring.inclusion (fun _ hc v hv => hc v (fun h => hv (hST h)))
-- ⋯
/-- The actual pullback of a number-field model along the inclusion of S-integer rings. -/
def numberFieldLevelModelBaseChange
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    Over (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST)))).obj X
```

A separated model over a ring of `T`-integers of a separated scheme of finite type over a number field (`Langlands.Global.NumberFieldSpreadSeparatedExistenceStatement`, proved by `Langlands.Global.numberFieldSpreadSeparatedExistence`):

`Langlands/Global/AdelicSpreadSeparatedExistenceStatement.lean`, lines 7, 9–10, 12, 27–37:

```lean
universe u
-- ⋯
open CategoryTheory
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
/-- A separated finite-type number-field scheme has a separated actual
integer-ring model after enlarging any prescribed finite place set. -/
def NumberFieldSpreadSeparatedExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (Y : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom],
    ∃ (T : AdelicLevelIndexAbove S)
      (M : Over (Spec (CommRingCat.of ((T.val : Set (FinitePlace K)).integer K)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
        Nonempty (numberFieldModelGenericFiber K T.val M ≅ Y)
```
`Langlands/Global/AdelicSpreadSeparatedExistenceProof.lean`, lines 10, 12–13, 15, 64–67:

```lean
universe u
-- ⋯
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
/-- The same construction retains the original number field and all
finite initial place sets. -/
theorem numberFieldSpreadSeparatedExistence :
    NumberFieldSpreadSeparatedExistenceStatement.{u} := by
```

Properness and smoothness of a morphism of models hold on the generic fibre exactly when they hold after base change to some finite superlevel (`Langlands.Global.NumberFieldSpreadEventualPropernessStatement` and `Langlands.Global.NumberFieldSpreadEventualPropertyStatement`, proved for `IsProper` and `@Smooth` by `Langlands.Global.numberFieldSpreadEventualProperness` and `Langlands.Global.numberFieldSpreadEventualSmoothness`):

`Langlands/Global/AdelicSpreadEventualPropernessStatement.lean`, lines 7, 9–10, 12, 30–44:

```lean
universe u
-- ⋯
open CategoryTheory
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
/-- The corresponding properness equivalence over the original number field
and the literal inclusions of its outside-set integer rings. -/
def NumberFieldSpreadEventualPropernessStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y),
    IsProper (((Over.pullback
      (Spec.map (CommRingCat.ofHom
        ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map f).left) ↔
      ∃ T : AdelicLevelIndexAbove S,
        IsProper (((Over.pullback
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))).map
            f).left)
```
`Langlands/Global/AdelicSpreadEventualPropernessProof.lean`, lines 11, 13–14, 16, 85–87:

```lean
universe u
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
/-- The same specialization retains the original number field and integer rings. -/
theorem numberFieldSpreadEventualProperness :
    NumberFieldSpreadEventualPropernessStatement.{u} := by
```
`Langlands/Global/AdelicSpreadEventualSmoothFiberGeometryStatement.lean`, lines 8, 10–11, 13, 15, 34–49:

```lean
universe u
-- ⋯
open CategoryTheory
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
open Langlands.AlgebraicGeometry.SchemeFiberGeometry
-- ⋯
/-- The same relative-property assertion for supplied number-field models
and their original outside-set integer rings. -/
def NumberFieldSpreadEventualPropertyStatement
    (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y),
    P (((Over.pullback
      (Spec.map (CommRingCat.ofHom
        ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map f).left) ↔
      ∃ T : AdelicLevelIndexAbove S,
        P (((Over.pullback
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))).map
            f).left)
```
`Langlands/Global/AdelicSpreadEventualSmoothFiberGeometryProof.lean`, lines 16, 18–19, 21, 103–105:

```lean
universe u
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
-- ⋯
namespace Langlands.Global
-- ⋯
/-- Smoothness is detected on an actual number-field integer superlevel. -/
theorem numberFieldSpreadEventualSmoothness :
    NumberFieldSpreadEventualPropertyStatement.{u} @Smooth := by
```

Principal levels: for a nonzero integer `t` of `K`, the set of places whose prime ideal contains `t`, the identification of its ring of integers with the localization `𝒪_K[1/t]` inside `K`, and a principal level above any given finite set, whose ring is of finite type over `ℤ` (`Langlands.Global.numberFieldPrincipalExceptional`, `Langlands.Global.numberFieldPrincipalSIntegerEquiv`, `Langlands.Global.numberFieldPrincipalLevelAbove`, `Langlands.Global.numberFieldPrincipalLevelAbove_finiteType`):

`Langlands/Global/NumberFieldPrincipalSIntegerFiniteType.lean`, lines 9, 11–12, 14, 16, 18–23, 25–28, 37–43, 110–114, 116, 118–122:

```lean
universe u
-- ⋯
open IsDedekindDomain
open scoped BigOperators
-- ⋯
namespace Langlands.Global
-- ⋯
variable (K : Type u) [Field K] [NumberField K]
-- ⋯
/-- The actual finite set of places where the inverse of an integral denominator
is not integral. -/
def numberFieldPrincipalExceptional (t : NumberField.RingOfIntegers K) :
    Finset (FinitePlace K) := by
  classical
  exact (HeightOneSpectrum.Support.finite (NumberField.RingOfIntegers K) (t : K)⁻¹).toFinset
-- ⋯
@[simp]
theorem mem_numberFieldPrincipalExceptional
    (t : NumberField.RingOfIntegers K) (ht : t ≠ 0) (p : FinitePlace K) :
    p ∈ numberFieldPrincipalExceptional K t ↔ t ∈ p.asIdeal := by
-- ⋯
/-- The actual principal outside-set ring agrees with the original embedded
localization, preserving every field element and its integer coefficients. -/
def numberFieldPrincipalSIntegerEquiv
    (t : NumberField.RingOfIntegers K) (ht : t ≠ 0) :
    dedekindAwaySubalgebra (K := K) t ht ≃ₐ[NumberField.RingOfIntegers K]
      ((numberFieldPrincipalExceptional K t : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K :=
-- ⋯
/-- An actual integer level above any prescribed finite initial set. -/
def numberFieldPrincipalLevelAbove (S : Finset (FinitePlace K)) :
    AdelicLevelIndexAbove S :=
  ⟨numberFieldPrincipalExceptional K (numberFieldPrincipalDenominator K S).1,
    (numberFieldPrincipalDenominator K S).2.2⟩
-- ⋯
open scoped NumberFieldPrincipalSIntegers
-- ⋯
/-- The chosen actual cofinal integer level is of finite type over the integers. -/
instance numberFieldPrincipalLevelAbove_finiteType (S : Finset (FinitePlace K)) :
    Algebra.FiniteType ℤ
      ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K) := by
```

The assembly for a smooth, geometrically connected, separated scheme over a number field: a model over a principal level of finite type over `ℤ` with the same properties (`Langlands.Global.exists_numberFieldSmoothConnectedModel`). The proof applies `numberFieldSpreadSeparatedExistence`, then the eventual form of `Smooth ⊓ GeometricallyConnected` to the structure morphism of the model, seen as a morphism to the terminal object of the slice, through the private lemma `property_pullback_structureMap_iff`. It then base-changes the model to `numberFieldPrincipalLevelAbove`:

`Langlands/Global/NumberFieldAlmostAllLocalPoints.lean`, lines 12, 18–20, 22, 24–29, 39–52:

```lean
universe u
-- ⋯
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
-- ⋯
namespace Langlands.Global
-- ⋯
private lemma property_pullback_structureMap_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {B C : Scheme.{u}} (b : C ⟶ B) (M : Over B) :
    P (((Over.pullback b).map
      (Over.homMk M.hom (by simp) : M ⟶ Over.mk (𝟙 B))).left) ↔
        P (((Over.pullback b).obj M).hom) := by
-- ⋯
/-- A smooth geometrically connected separated finite-type scheme admits
an actual smooth geometrically connected model over a finite-type ring of
S-integers. -/
theorem exists_numberFieldSmoothConnectedModel
    (K : Type u) [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K)))
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [GeometricallyConnected X.hom] :
    ∃ (S : Finset (FinitePlace K))
      (M : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
      Algebra.FiniteType ℤ ((S : Set (FinitePlace K)).integer K) ∧
      Smooth M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      GeometricallyConnected M.hom ∧
      Nonempty (numberFieldModelGenericFiber K S M ≅ X) := by
```

## B. AxiomMath/Stacks at `c496df0`

Paths are relative to the repository root.

### B.1 Tag 0GLI: higher direct images under a smooth proper morphism

`Stacks.EtaleCohomology.isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper`:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmoothProperHigherDirectImageLocallyConstant.lean`, lines 38, 40, 42, 44, 46, 311, 313–314, 331–340:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.ConstantSheaf
-- ⋯
universe u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
-- ⋯
section Main
-- ⋯
attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse smallEtaleHasSheafifyModuleMax
-- ⋯
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (Λ : Type) [CommRing Λ]
    [IsNoetherianRing Λ] (F : EtaleModules.{u, 0} Λ X)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.smallEtaleTopology Λ F)
    (htors : ∀ x : GeometricPoint X, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ X).obj F), n • a = 0)
    (i : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} S.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived i).obj F) := by
```

### B.2 Tag 0GKD: specialization for a smooth proper morphism

`AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper_unconditional` (namespace
`AlgebraicGeometry`, not `Stacks.EtaleCohomology`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/LocalAcyclicity/SmoothProperSpecializationUnconditional.lean`, lines 38, 40–41, 43, 45, 47, 49, 68–78:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe u
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Stacks.EtaleCohomology
-- ⋯
attribute [local instance] HasDerivedCategory.standard
-- ⋯
theorem isIso_specializationMap_of_smooth_of_isProper_unconditional (B : BigEtaleSite.{u})
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) [Smooth f]
    [IsProper f] (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hFlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F)
    (hFtors : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
      ∃ n : ℕ, 0 < n ∧
        (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0)
    (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s)) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) :=
```

### B.3 Spreading out a smooth proper scheme

`AlgebraicGeometry.exists_isPullback_specAdjoin_smoothOfRelativeDimension`:

`StacksFrontier/AlgebraicGeometry/Limits/NoetherianApproximation/ProperSmoothFiniteTypeSubring.lean`, lines 28, 30, 32, 34, 109–114:

```lean
@[expose] public section
-- ⋯
open CategoryTheory CategoryTheory.Limits
-- ⋯
universe u
-- ⋯
namespace AlgebraicGeometry
-- ⋯
theorem exists_isPullback_specAdjoin_smoothOfRelativeDimension (R : Type u) [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ∃ (j : (Finset R)ᵒᵖ) (Y : Scheme.{u}) (h : Y ⟶ (specAdjoinFinsetDiagram R).obj j)
      (q' : X ⟶ Y), IsProper h ∧ SmoothOfRelativeDimension n h ∧
        IsPullback q' f h ((specAdjoinFinsetCone R).π.app j) := by
```

### B.4 The Galois-equivariant derived global sections

All declarations below are in the namespace `Stacks.EtaleCohomology`. None requires
torsion coefficients or a Noetherian ring: `Λ : Type` with `[Ring Λ]`.

The finite stages `Y_E` and the limit cone `Y_K = lim Y_E` (`fieldStageSystem`,
`fieldStageCone`, `fieldStageConeIsLimit`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisEquivariantGlobalSections.lean`, lines 69, 71–72, 74, 76, 80, 82–83, 91, 176, 178, 182, 189–190, 220:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius
-- ⋯
universe u v
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
section Stages
-- ⋯
variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u)
  [Field K] [Algebra k K]
-- ⋯
attribute [local instance] fextOrderBot
-- ⋯
variable [Algebra.IsSeparable k K]
-- ⋯
attribute [local instance] etale_spectrumMap_fext
-- ⋯
def fieldStageSystem : (FExt k K)ᵒᵖ ⥤ Y.left.Etale where
-- ⋯
def fieldStageCone :
    Cone (fieldStageSystem Y K ⋙ Scheme.Etale.forget Y.left ⋙ Over.forget Y.left) where
-- ⋯
def fieldStageConeIsLimit : IsLimit (fieldStageCone Y K) :=
```

The action on global sections over `Y_K`, induced by `id_Y × Spec σ`
(`fieldBaseChangeGlobalSectionsGaloisAction`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/FieldBaseChangeGlobalSectionsGaloisAction.lean`, lines 27, 29–31, 33, 35, 37–38, 42–46:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius
-- ⋯
universe u r
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (σ : kbar ≃ₐ[k] kbar)
-- ⋯
def fieldBaseChangeGlobalSectionsGaloisAction (G : EtaleModules.{u, r} Λ Y.left) :
    (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj G) ⟶
      (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj G) :=
```

Its continuity (`isOpen_stabilizer_fieldBaseChangeGlobalSectionsGaloisAction`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisEquivariantGlobalSections.lean`, lines 69, 71–72, 74, 76, 379, 381, 383–384, 445, 474–478:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius
-- ⋯
universe u v
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
section Action
-- ⋯
open scoped Stacks.DiscreteModuleTopology
-- ⋯
variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u)
  [Field K] [Algebra k K]
-- ⋯
variable [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
-- ⋯
theorem isOpen_stabilizer_fieldBaseChangeGlobalSectionsGaloisAction
    (G : EtaleModules.{u, 0} Λ Y.left)
    (z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)) :
    IsOpen {σ : K ≃ₐ[k] K | fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G z = z} := by
```

The category of discrete Galois modules and the functor `Γ^Gal` (`GaloisModules`,
`galoisGlobalSections`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisEquivariantGlobalSections.lean`, lines 69, 71–72, 74, 76, 524, 526, 533–535, 537–539, 546:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius
-- ⋯
universe u v
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
section Functor
-- ⋯
open scoped Stacks.DiscreteModuleTopology
-- ⋯
abbrev GaloisModules (Λ : Type) [Ring Λ] (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] :=
  Stacks.Injectives.ContinuousModule.{0, u, u + 1} Λ (K ≃ₐ[k] K)
-- ⋯
variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K]
-- ⋯
def galoisGlobalSections : EtaleModules.{u, 0} Λ Y.left ⥤ GaloisModules Λ k K where
```

The derived functor `RΓ^Gal` and its comparison with `RΓ(Y_k̄, -)`
(`galoisDerivedGlobalSections`, `galoisDerivedGlobalSectionsForgetIso`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisEquivariantDerivedGlobalSections.lean`, lines 64, 66, 68, 70, 78, 80–84, 89–92, 128, 130–149, 171–176:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius
-- ⋯
universe w₁ w₂ w₃ w₄ u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
section Derived
-- ⋯
variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λ k kbar)]
-- ⋯
abbrev galoisDerivedGlobalSections :
    DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y.left) ⥤
      DerivedCategory.Plus (GaloisModules Λ k kbar) :=
  (galoisGlobalSections Λ Y kbar).rightDerivedFunctorPlus
-- ⋯
section Forget
-- ⋯
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for discrete Galois modules (Stacks 04JF), pinned at the module universe
`u + 1`: the general instance is indexed by `max 0 u (u + 1)`. -/
local instance (priority := 3000) galoisModules_enoughInjectives (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λ)]
-- ⋯
def galoisDerivedGlobalSectionsForgetIso :
    galoisDerivedGlobalSections Λ Y kbar ⋙
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k]
            kbar)).mapDerivedCategoryPlus ≅
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus :=
```

The two actions and their identification (`galoisModuleAction`, `galoisForgetAction`,
`galoisRestrictionCohomologyNatTrans`,
`galoisForgetAction_comp_galoisDerivedGlobalSectionsForgetIso`). In both sections the
derived categories are the standard model (`HasDerivedCategory.standard`, a local
instance):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisEquivariantCohomologyAction.lean`, lines 67, 69, 71, 73, 75, 425–450, 455–459, 464–469, 474–478, 565–596:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius Opposite
-- ⋯
universe u w₁ w₂
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
-- ⋯
section Actions

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisActions (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules, pinned. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisActions (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

/-- `Q : C⁺(𝒜) ⥤ D⁺(𝒜)` is a localization at the quasi-isomorphisms. -/
local instance isLocalization_plusQ_galoisAction (𝒜 : Type*) [Category* 𝒜] [Abelian 𝒜] :
    (DerivedCategory.Plus.Q (C := 𝒜)).IsLocalization (CochainComplex.Plus.quasiIso 𝒜) :=
  Functor.IsLocalization.of_iso _ (DerivedCategory.Plus.quotientCompQhIso 𝒜)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar]
-- ⋯
def galoisModuleAction (σ : kbar ≃ₐ[k] kbar) :
    Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar) ⟶
      Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar) where
  app M := (M.obj.obj.ρ σ).asHom
  naturality _ _ f := (f.hom.hom.comm σ).symm
-- ⋯
def galoisForgetAction (σ : kbar ≃ₐ[k] kbar) :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlus ⟶
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlus :=
  Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans (galoisModuleAction Λ kbar σ)
-- ⋯
def galoisRestrictionCohomologyNatTrans (σ : kbar ≃ₐ[k] kbar) :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus ⟶
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus :=
-- ⋯
section Equivariance

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisEquiv (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules, pinned. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisEquiv (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

/-- **The Galois action on `RΓ^Gal(Y_k̄, -)` is the action of Remark 03UI (2)**: forgetting the
action, `RΓ^Gal(Y_k̄, -) ⋙ U ≅ RΓ(Y_k̄, -|_{Y_k̄})`
(`Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso`) carries the action of `σ` coming
from the Galois-module structure to the action induced by `id_Y × Spec σ`. -/
theorem galoisForgetAction_comp_galoisDerivedGlobalSectionsForgetIso (σ : kbar ≃ₐ[k] kbar) :
    Functor.whiskerLeft (galoisDerivedGlobalSections Λ Y kbar) (galoisForgetAction Λ kbar σ) ≫
        (galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom =
      (galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom ≫
        galoisRestrictionCohomologyNatTrans Λ Y kbar σ := by
```

### B.5 Tag 03Q9: the Galois action on one cohomology group and on the stalk of a higher direct image

These are in the namespace `Stacks.Frobenius`
(`Stacks.Frobenius.galoisCohomologyAction`,
`Stacks.Frobenius.higherDirectImageFibreAddEquiv_smul`). The coefficients are abelian
sheaves in `Ab.{u + 1}`.

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisEquivariantStalkComparison.lean`, lines 76, 78–80, 82, 84, 435, 437, 439, 469–474:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology
-- ⋯
universe u
-- ⋯
namespace Stacks.Frobenius
-- ⋯
section DegreeJ
-- ⋯
open Stacks.RightDerivedComp
-- ⋯
variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] (X : Over (Spec (.of k)))
-- ⋯
def galoisCohomologyAction (σ : K ≃ₐ[k] K) (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) ⟶
      ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) :=
```

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisModuleHigherDirectImageStalk.lean`, lines 61, 63–64, 66, 68, 70, 72–73, 173, 175, 204–213:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology Stacks.RightDerivedComp
-- ⋯
universe u
-- ⋯
namespace Stacks.Frobenius
-- ⋯
attribute [local instance] HasDerivedCategory.standard
-- ⋯
variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (X : Over (Spec (.of k)))
-- ⋯
section Packaging
-- ⋯
variable [QuasiCompact X.hom] [QuasiSeparated X.hom] [Algebra.IsSeparable k K]
-- ⋯
theorem higherDirectImageFibreAddEquiv_smul (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) (σ : K ≃ₐ[k] K)
    (x : ((smallEtalePushforwardAb X.hom).rightDerived j ⋙
        smallEtaleStalkAb (specAlgebraMap k K)).obj F) :
    higherDirectImageFibreAddEquiv K X j F
        (@HSMul.hSMul _ _ _
          (@instHSMul _ _ (galoisHigherDirectImageStalkDistribMulAction K X j F).toSMul) σ x) =
      @HSMul.hSMul _ _ _
        (@instHSMul _ _ (galoisCohomologyDistribMulAction K X j F).toSMul) σ
        (higherDirectImageFibreAddEquiv K X j F x) :=
```

### B.6 Tag 0GLH: finiteness of compactly supported cohomology, and the proper case

`Stacks.EtaleCohomology.module_finite_compactlySupportedCohomologyGroup_of_isConstructible`:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedLowerShriek/CompactSupportFinitenessAlgClosed.lean`, lines 30, 32, 34, 36, 38–40, 42, 54–68:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
-- ⋯
universe u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
-- ⋯
attribute [-instance] hasSheafifyEtale
-- ⋯
theorem module_finite_compactlySupportedCohomologyGroup_of_isConstructible
    {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] :
    (∀ K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj),
      (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
        IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
      ∀ i : ℤ, Module.Finite Λ ((compactlySupportedCohomologyGroup.{u, 0} k f j Λ i).obj K)) ∧
    ((∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) →
      ∀ K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj),
        (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.homologyFunctor _ q).obj K)) →
        ∀ i : ℤ, Module.Finite Λ
          ((compactlySupportedCohomologyGroupUnbounded.{u, 0} k f j Λ i).obj K)) := by
```

`AlgebraicGeometry.CompactificationOf.ofProper` and
`Stacks.EtaleCohomology.derivedLowerShriekOfProperIso`:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/ProperCohomologyExtComparison.lean`, lines 31, 33–34, 36, 38, 42–43:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius
-- ⋯
universe u r
-- ⋯
namespace AlgebraicGeometry
-- ⋯
def CompactificationOf.ofProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CompactificationOf (Over.mk f) :=
```

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedLowerShriek/FiniteComposition.lean`, lines 57, 59–60, 62, 262, 264, 266, 268, 270–271, 343–345:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
open _root_.AlgebraicGeometry
-- ⋯
attribute [local instance] HasDerivedCategory.standard
-- ⋯
section FiniteComposition
-- ⋯
variable (Λ : Type) [Ring Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (jg : CompactificationOf (Over.mk g))
-- ⋯
def derivedLowerShriekOfProperIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    derivedLowerShriek.{u, 0} f (CompactificationOf.ofProper f) Λ ≅
      etaleModuleDerivedDirectImage.{u, 0} Λ f :=
```

### B.7 Tag 09YQ on Mathlib's full small étale sites, and its form for the inverse images of one sheaf

The data of a system of abelian sheaves presented on the limit (`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem`), whose cocycle and cocone laws on cohomology are fields, and the elementwise colimit statement `IsCohomologyColimit`:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean`, lines 190, 192–193, 195, 197, 317, 328–333, 335–365, 367–369, 385–398:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe v u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
namespace SmallEtaleLimitCohomology
-- ⋯
variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D}
  [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]
-- ⋯
/-- **A system of abelian sheaves on the small étale sites of the levels, presented on the
limit.** The data of [Stacks, Tag 09YQ]: a system `sys` in the sense of [Stacks, Tag 0EZL], a
sheaf `sheaf` on the small étale site of the limit, legs `ι_i : f_i^{-1}F_i ⟶ sheaf`, the
hypothesis `P` that these exhibit `sheaf` as `colim f_i^{-1}F_i`, and the two laws making the
induced maps on cohomology a cocone over a filtered diagram.

`P` is a parameter rather than a definition, and the two laws are fields rather than lemmas; the
module docstring says why for each. -/
structure PresentedSystem
    (P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop)
    where
  /-- The system of abelian sheaves on the small étale sites of the levels. -/
  sys : EtaleSheafSystem D AddCommGrpCat.{u + 1}
  /-- The abelian sheaf on the small étale site of the limit. -/
  sheaf : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}
  /-- The map to it from the inverse image of the sheaf at each level. -/
  ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (sys.obj i) ⟶ sheaf
  /-- The sheaf on the limit, with these legs, presents the colimit of the system. -/
  pres : P sys sheaf ι
  /-- **The cocycle law on cohomology**: the maps of the cohomology diagram compose. -/
  transition_comp : ∀ {i j k : Iᵒᵖ} (b : i ⟶ j) (a : j ⟶ k) (p : ℕ)
      (x : Sheaf.H.{u + 1, u + 1} (sys.obj k) p),
    etaleCohomologyTransition sys b p (etaleCohomologyTransition sys a p x) =
      etaleCohomologyTransition sys (b ≫ a) p x
  /-- **The cocone law**: the leg at a level factors every earlier leg through the diagram map. -/
  leg_transition : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (p : ℕ)
      (x : Sheaf.H.{u + 1, u + 1} (sys.obj j) p),
    etaleCohomologyMapTo (conePi c i) (ι i) p (etaleCohomologyTransition sys a p x) =
      etaleCohomologyMapTo (conePi c j) (ι j) p x
-- ⋯
variable {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}
-- ⋯
/-- **The statement of [Stacks, Tag 09YQ] in degree `p`**: the cohomology `H^p(X, 𝒢)` of the
limit is the filtered colimit of the `H^p(X_i, F_i)` along the cocone of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg`. The two clauses are joint
surjectivity of the legs and the vanishing, at some later level, of a class killed by its leg;
for a filtered index and abelian coefficients they are exactly the assertion that the cocone is a
colimit cocone. See the module docstring on why the statement is in this form rather than as a
`CategoryTheory.Limits.IsColimit`. -/
structure IsCohomologyColimit (E : PresentedSystem P) (p : ℕ) : Prop where
  /-- Every class on the limit comes from a level. -/
  exists_leg_eq : ∀ y : Sheaf.H.{u + 1, u + 1} E.sheaf p,
    ∃ (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p), E.leg i p x = y
  /-- A class at a level whose image on the limit vanishes already vanishes at a later level. -/
  exists_transition_eq_zero : ∀ (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p),
    E.leg i p x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), etaleCohomologyTransition E.sys a p x = 0
```

The theorem `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit`, on the full small étale sites in every degree. The big étale site `B` fixes the size:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleColimitUnconditional.lean`, lines 84, 86, 88, 90, 92–96, 98–133:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
-- ⋯
universe v u
-- ⋯
namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology
-- ⋯
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D) (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
-- ⋯
include B hD hX hc in
/-- **[Stacks, Tag 09YQ] on Mathlib's small étale sites, in every degree, unconditionally.** Let
`I` be a nonempty directed index, let `(X_i)` be an inverse system of schemes over `Iᵒᵖ` with
**affine** transition morphisms and every `X_i` **quasi-compact and quasi-separated**, let `c` be a
**limit** cone with vertex `X`, and let all the `X_i` and `X` be objects of a big étale site `B`.
Then for every presented system `E` — a system `(F_i)` of abelian sheaves on Mathlib's small étale
sites of the `X_i` in the sense of [Stacks, Tag 0EZL], together with an abelian sheaf `𝒢` on the
small étale site of `X` and legs `ι_i : f_i^{-1}F_i ⟶ 𝒢` exhibiting `𝒢 = colim_i f_i^{-1}F_i` —
and every degree `p`, the cohomology `H^p(X, 𝒢)` is the filtered colimit of the `H^p(X_i, F_i)`
along the legs.

This is `isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` with all four of its hypotheses
supplied; the module docstring says which theorem supplies each, and how the two instances
on the vertex are derived rather than assumed.

**No identity law** on the system of [Stacks, Tag 0EZL] is used or available: Definition 59.51.1 of
that tag imposes only the cocycle condition, and none of the four suppliers asks for more. -/
@[stacks 09YQ "the whole tag, for ALL degrees `p ≥ 0` and every system of abelian sheaves in the \
sense of Tag 0EZL, with no hypothesis beyond the source's. The source assumes a directed set, \
affine transition morphisms, `X = lim X_i` and that every `X_i` is quasi-compact and \
quasi-separated; those are `IsDirected`, `IsAffineHom (D.map a)`, `hc : IsLimit c`, and the \
per-level `CompactSpace`/`QuasiSeparatedSpace` instances. The big etale site `B` with `hD`/`hX` is \
a SIZE device and not a source hypothesis: it fixes which small sites are meant, and \
`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` produces one for any small family. The \
corresponding instances on the VERTEX are derived, not assumed. The conclusion is the tag's \
equality of groups in elementwise form -- joint surjectivity of the legs together with eventual \
vanishing, which for a filtered index and abelian coefficients is exactly the assertion that the \
cocone is colimiting -- and \
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimit_stableCohomologyCocone` transports it, \
in both directions, to a genuine `CategoryTheory.Limits.IsColimit` whose vertex is the full \
`H^p(X, 𝒢)`. No identity law is used: Definition 59.51.1 imposes only the cocycle condition, so \
the naive diagram `i ↦ H^p(X_i, F_i)` is not a functor in general, and \
`hasCohomologyIdentityLaw_iff_forall_stableCohomologySubgroup_eq_top` says precisely when the two \
spellings coincide. No hypothesis of this statement is an instance of its own conclusion."]
theorem isCohomologyColimit_of_isLimit (p : ℕ)
    (E : PresentedSystem (c := c) IsColimitPresentation) : IsCohomologyColimit E p := by
```

`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small`, which produces such a `B` for any small family of schemes:

`StacksFrontier/AlgebraicGeometry/Topologies/Etale/Existence.lean`, lines 82, 84, 86, 88, 90, 201–203:

```lean
@[expose] public section
-- ⋯
open Cardinal CategoryTheory
-- ⋯
universe v' u' u
-- ⋯
namespace AlgebraicGeometry
-- ⋯
namespace BigEtaleSite
-- ⋯
/-- Every small set of schemes lies in a single big étale site. -/
public theorem exists_contains_of_small (S₀ : Set AlgebraicGeometry.Scheme.{u}) [Small.{u} S₀] :
    ∃ B : BigEtaleSite.{u}, ∀ X ∈ S₀, B.Contains X :=
```

The passage from the elementwise statement to an `IsColimit` (`isColimit_stableCohomologyCocone`). This module is outside the nine-root closure of Section 7.1 of the audit note:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyIsColimit.lean`, lines 168, 170–171, 173, 175, 177–184, 291–302:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe v u
-- ⋯
namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology
-- ⋯
variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]
  {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}
-- ⋯
/-- **The elementwise statement of Tag 09YQ makes the cohomology cocone a colimit cocone.**

This is the direction a registration of [Stacks, Tag 09YQ] needs: it turns
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCohomologyColimit` into the tag's own
equality of groups, `H^p(X, 𝒢) = colim_i H^p(X_i, F_i)` in `AddCommGrpCat.{u + 1}`.

Joint surjectivity is the first clause of `IsCohomologyColimit` composed with
`leg_cohomologyIdem`, which moves the chosen class into the stable part without changing its
leg; the eventual vanishing is the second clause verbatim. -/
def isColimit_stableCohomologyCocone [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{v, u + 1}]
    (E : PresentedSystem P) (p : ℕ) (h : IsCohomologyColimit E p) :
    IsColimit (stableCohomologyCocone E p) := by
```

The form for the inverse images `s_i^{-1}G` of one abelian sheaf `G` on a base `S`: the presented system `pullbackPresentedSystem`, the theorem `isCohomologyColimit_pullbackPresentedSystem`, which finds the big étale site itself, and its two halves for restriction maps:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/PullbackSystemCohomologyColimit.lean`, lines 57, 59–60, 62, 64, 208, 279, 281–286, 288–291, 293–300, 350–360, 367–378:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe v u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
namespace SmallEtaleLimitCohomology
-- ⋯
section Colimit
-- ⋯
variable {S : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{u}} [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  (G : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1}) (s : ∀ i : Iᵒᵖ, D.obj i ⟶ S)
  (hs : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), s i = D.map a ≫ s j)
  {c : Cone D} (hc : IsLimit c) (sc : c.pt ⟶ S) (hsc : ∀ i : Iᵒᵖ, sc = conePi c i ≫ s i)
-- ⋯
/-- The system of inverse images of `G`, presented on the limit by the inverse image of `G`. -/
def pullbackPresentedSystem : PresentedSystem (c := c) IsColimitPresentation :=
  presentedSystemOfIsColimitPresentation (pullbackSystem G s hs) _
    (pullbackSystemLeg G s hs sc hsc) (isColimitPresentation_pullbackSystem G s hs sc hsc)
-- ⋯
include hc in
/-- **[Stacks, Tag 09YQ] for the inverse images of one sheaf.** Let `(X_i)` be a nonempty
directed inverse system of quasi-compact and quasi-separated schemes over `S` with affine
transition morphisms and limit `X`, and let `G` be an abelian sheaf on the small étale site of
`S`. Then `H^p(X, s^{-1}G) = colim_i H^p(X_i, s_i^{-1}G)`, in the elementwise form of
`IsCohomologyColimit`. -/
theorem isCohomologyColimit_pullbackPresentedSystem (p : ℕ) :
    IsCohomologyColimit (pullbackPresentedSystem G s hs sc hsc) p := by
-- ⋯
include hs hsc hc in
/-- **A class vanishing on the limit vanishes at a level.** Let `(X_i)` be a nonempty directed
inverse system of quasi-compact and quasi-separated schemes over `S` with affine transition
morphisms and limit `X`, and let `G` be an abelian sheaf on the small étale site of `S`. If the
restriction of `ξ ∈ H^p(S, G)` to `H^p(X, G|_X)` vanishes, then so does its restriction to
`H^p(X_i, G|_{X_i})` for some `i`. This is the injectivity half of
`colim_i H^p(X_i, G|_{X_i}) = H^p(X, G|_X)` ([Stacks, Tag 09YQ]; [Stacks, Tag 03Q6] is the case
of a system of base changes). -/
theorem exists_restriction_eq_zero_of_isLimit (p : ℕ) (ξ : Sheaf.H.{u + 1, u + 1} G p)
    (hξ : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} sc G p ξ = 0) :
    ∃ i : Iᵒᵖ, etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (s i) G p ξ = 0 := by
-- ⋯
include hs hc in
/-- **Every class on the limit comes from a level.** In the situation of
`exists_restriction_eq_zero_of_isLimit`, every class in `H^p(X, G|_X)` is the image, under
restriction along `X ⟶ X_i` followed by the canonical identification of the inverse images, of a
class in `H^p(X_i, G|_{X_i})` for some `i`. This is the surjectivity half of
[Stacks, Tag 09YQ] for the inverse images of one sheaf. -/
theorem exists_eq_etaleCohomologyMapTo_of_isLimit (p : ℕ)
    (y : Sheaf.H.{u + 1, u + 1} ((etaleAbelianInverseImage.{u, u + 1} sc).obj G) p) :
    ∃ (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} ((etaleAbelianInverseImage.{u, u + 1} (s i)).obj G) p),
      etaleCohomologyMapTo (conePi c i)
        ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c i) (s i) sc (hsc i)).inv.app G)
        p x = y :=
```

### B.8 Compactly supported cohomology of a proper scheme is ordinary cohomology

The group of 0GLH (B.6) on a sheaf `F` placed in degree `0` is `Rⁿ Γ(X̄, j_!F)`, for any field `k`, any `f` locally of finite type, quasi-compact and separated, and any compactification `j` (`Stacks.EtaleCohomology.compactlySupportedCohomologyGroupSingleIso`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionModules/CompactSupportCurveFiniteness.lean`, lines 42, 44–45, 47, 49, 98, 100, 102, 128–129, 131–138:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe u r
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
section CompactSupport
-- ⋯
attribute [local instance] HasDerivedCategory.standard
-- ⋯
variable (Λ : Type r) [Ring Λ]
-- ⋯
variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
-- ⋯
/-- **`H^n_c(X, F) = H^n(X̄, j_!F)`** for a compactification `j : X ⟶ X̄` (Definition 0GJZ): the
composite of `Rf̄_*` with `RΓ(Spec k, -)` is `RΓ(X̄, -)`, the direct image preserving injectives,
and `Rj_!(F[0]) = (j_!F)[0]`, extension by zero being exact. -/
def compactlySupportedCohomologyGroupSingleIso (n : ℕ) (F : EtaleModules.{u, r} Λ X) :
    (compactlySupportedCohomologyGroup.{u, r} k f j Λ n).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F) ≅
      ((etaleModuleGlobalSections.{u, r} Λ j.space).rightDerived n).obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F) :=
```

A proper scheme is its own compactification, with the identity as the open immersion (`AlgebraicGeometry.CompactificationOf.ofProper`), and extension by zero along the identity is the identity (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroIdIso`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/ProperCohomologyExtComparison.lean`, lines 31, 33–34, 36, 38, 40–45, 47, 49, 51, 53–56:

```lean
@[expose] public noncomputable section
-- ⋯
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius
-- ⋯
universe u r
-- ⋯
namespace AlgebraicGeometry
-- ⋯
/-- **A proper scheme is its own compactification**: the identity of `X` is an open immersion and
the structure morphism `f : X ⟶ Y` is proper. -/
def CompactificationOf.ofProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CompactificationOf (Over.mk f) :=
  ⟨StructuredArrow.mk (𝟙 (Over.mk f)), ⟨inferInstanceAs (IsOpenImmersion (𝟙 X)),
    inferInstanceAs (IsProper f)⟩⟩
-- ⋯
end AlgebraicGeometry
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
attribute [local instance] HasDerivedCategory.standard
-- ⋯
/-- **Extension by zero along the identity is the identity**, on étale sheaves of
`Λ`-modules. -/
def etaleModuleExtensionByZeroIdIso (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    etaleModuleExtensionByZero.{u, r} Λ (𝟙 X) ≅ 𝟭 _ :=
```

### B.9 Tag 03Q6 (09YQ) for the base change to an algebraic extension

The finite subextensions of `K/k` (`AlgebraicGeometry.FExt`), the diagram of base changes `Spec E ×_{Spec k} X` and its cone, and the theorem that the base change to an algebraic extension is their limit (`AlgebraicGeometry.fextPullbackConeIsLimit`). Only `Algebra.IsAlgebraic k K` is assumed; there is no separability hypothesis:

`StacksFrontier/AlgebraicGeometry/Variety/Geometrically/QuasiCompactOpen.lean`, lines 32, 34, 36, 108–110, 322–349:

```lean
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
universe u
-- ⋯
/-- The finite subextensions of a field extension, ordered by inclusion. -/
public abbrev FExt (k K : Type u) [Field k] [Field K] [Algebra k K] :=
  {E : IntermediateField k K // FiniteDimensional k E}
-- ⋯
/-- The diagram of base changes of `f` to the finite subextensions. -/
public def fextPullbackDiagram
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) :
    (FExt k K)ᵒᵖ ⥤ Scheme :=
  fextOverDiagram (k := k) (K := K) ⋙ Over.pullback f ⋙ Over.forget X

/-- The cone of base changes of `f` to the finite subextensions. -/
public noncomputable def fextPullbackCone
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) :
    Cone (fextPullbackDiagram (k := k) (K := K) X f) where
  pt := pullback (spectrumMap k K) f
  π.app i := ((Over.pullback f).map
    ((fextOverCone (k := k) (K := K)).π.app i)).left
  π.naturality i j g := by
    change ((Over.pullback f).map
        ((fextOverCone (k := k) (K := K)).π.app j)).left =
      ((Over.pullback f).map ((fextOverCone (k := k) (K := K)).π.app i)).left ≫
        ((Over.pullback f).map ((fextOverDiagram (k := k) (K := K)).map g)).left
    rw [← Over.comp_left, ← Functor.map_comp, (fextOverCone (k := k) (K := K)).w g]

/-- The base change to an algebraic extension is the limit of the base changes to the finite
subextensions. -/
public noncomputable def fextPullbackConeIsLimit
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) :
    IsLimit (fextPullbackCone (k := k) (K := K) X f) := by
```

The two halves of the colimit statement for the inverse images of one abelian sheaf `G` on `Y`, for `Ω/L` algebraic and `Y` quasi-compact and quasi-separated (`Stacks.EtaleCohomology.exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic` and `Stacks.EtaleCohomology.exists_finiteDimensional_eq_etaleCohomologyMapTo_of_isAlgebraic`). This module and `PullbackSystemCohomologyColimit` (B.7), which it imports, are the two modules of its closure outside the nine-root closure of Section 7.1 of the audit note:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/AlgebraicExtensionCohomologyColimit.lean`, lines 40–41, 43, 45, 47, 62, 101–116, 126–141:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω]
-- ⋯
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of L))
-- ⋯
variable [Algebra.IsAlgebraic L Ω] [CompactSpace Y] [QuasiSeparatedSpace Y]
  (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **A class dying on the base change to an algebraic extension dies at a finite stage.** Let
`Y` be a quasi-compact and quasi-separated scheme over a field `L`, let `G` be an abelian sheaf on
the small étale site of `Y` and let `Ω/L` be algebraic. If the restriction of
`ξ ∈ H^p(Y, G)` to the base change `Y_Ω` vanishes, then so does its restriction to `Y_E` for some
subextension `E` of `Ω/L` of finite degree. This is the injectivity half of
[Stacks, Tag 03Q6] for the system of finite subextensions of `Ω/L`. -/
theorem exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic (p : ℕ)
    (ξ : Sheaf.H.{u + 1, u + 1} G p)
    (hξ : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (pullback.snd (spectrumMap L Ω) f) G p ξ
      = 0) :
    ∃ E : IntermediateField L Ω, FiniteDimensional L E ∧
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (pullback.snd (spectrumMap L E) f) G p ξ
        = 0 := by
-- ⋯
/-- **Every class on the base change to an algebraic extension comes from a finite stage.** In
the situation of `exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic`, every class in
`H^p(Y_Ω, G|_{Y_Ω})` is the image of a class in `H^p(Y_E, G|_{Y_E})` for some subextension `E` of
finite degree, under restriction along `Y_Ω ⟶ Y_E` followed by the canonical identification of the
inverse images. This is the surjectivity half of [Stacks, Tag 03Q6]. -/
theorem exists_finiteDimensional_eq_etaleCohomologyMapTo_of_isAlgebraic (p : ℕ)
    (y : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd (spectrumMap L Ω) f)).obj G) p) :
    ∃ (E : FExt L Ω) (x : Sheaf.H.{u + 1, u + 1}
        ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd (spectrumMap L E.1) f)).obj G) p),
      etaleCohomologyMapTo ((fextPullbackCone (k := L) (K := Ω) Y f).π.app (op E))
        ((etaleAbelianInverseImageCompIso'.{u, u + 1}
          ((fextPullbackCone (k := L) (K := Ω) Y f).π.app (op E))
          (pullback.snd (spectrumMap L E.1) f) (pullback.snd (spectrumMap L Ω) f)
          (Over.w ((Over.pullback f).map ((fextOverCone (k := L) (K := Ω)).π.app (op E)))).symm
          ).inv.app G) p x = y := by
```

### B.10 Spreading out a smooth proper morphism, and descent of a locally constant sheaf to a stage (Tag 0GL2)

A proper smooth morphism to the spectrum of a ring `A` is the base change of a proper smooth morphism over a finitely generated `ℤ`-algebra mapping injectively to `A` (`AlgebraicGeometry.HodgeSpreadingOut.exists_isPullback_finiteType_properSmooth`). No relative dimension is fixed:

`StacksFrontier/AlgebraicGeometry/DeRham/HodgeSpreadingOut/FiniteTypeModel.lean`, lines 34, 36, 38, 107–117:

```lean
open CategoryTheory CategoryTheory.Limits
-- ⋯
universe u
-- ⋯
namespace AlgebraicGeometry.HodgeSpreadingOut
-- ⋯
/-- **A proper smooth scheme over a ring is the base change of a proper smooth scheme over a
finitely generated `ℤ`-algebra mapping injectively to the ring.** For `f : X ⟶ Spec A` proper and
smooth there are a finitely generated `ℤ`-algebra `R`, an injective ring map `φ : R ⟶ A` and a
proper smooth `h : Y ⟶ Spec R` with `X = Y ×_{Spec R} Spec A`. The ring `R` is the subring of
`Γ(Spec A, ⊤) ≅ A` generated by a finite set. -/
@[ega "IV 8.9.1" "(i), special case"]
theorem exists_isPullback_finiteType_properSmooth (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [Smooth f] :
    ∃ (R : Type u) (_ : CommRing R) (φ : R →+* A) (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R))
      (q' : X ⟶ Y), Algebra.FiniteType ℤ R ∧ Function.Injective φ ∧ IsProper h ∧ Smooth h ∧
        IsPullback q' f h (Spec.map (CommRingCat.ofHom φ)) := by
```

The faithfulness and essential-surjectivity conditions of Tag 0GL2 for a directed system of stages, stated on the small étale sites `SmallEtale.topology B X` of a big étale site `B` (`AlgebraicGeometry.SmallEtaleStagesFaithful`, `AlgebraicGeometry.SmallEtaleStagesEssSurj`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteLocallyConstantLimitCategory.lean`, lines 111, 113, 147, 161, 163–168, 177, 198–209, 225–232:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
-- ⋯
universe w w' t v u iu r
-- ⋯
namespace AlgebraicGeometry
-- ⋯
section Stages
-- ⋯
variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme)
-- ⋯
variable (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)
-- ⋯
/-- **Faithfulness of the comparison.** Two maps between sheaves with the property `P` at a stage
which agree after inverse image to the vertex already agree at some later stage. -/
public def SmallEtaleStagesFaithful (P : SmallEtaleSheafProperty B A) : Prop :=
  ∀ (i : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A),
    P (Dg.obj (op i)) F → P (Dg.obj (op i)) G → ∀ a b : F ⟶ G,
      (smallEtaleStageProjection B A Dg c hX i).map a =
        (smallEtaleStageProjection B A Dg c hX i).map b →
      ∃ (j : I) (h : i ≤ j),
        (smallEtaleStageTransition B A Dg h).map a =
          (smallEtaleStageTransition B A Dg h).map b

-- ⋯
/-- **Essential surjectivity of the comparison.** Every sheaf with the property `P` on the vertex
is isomorphic to the inverse image of a sheaf with the property `P` at some stage. -/
public def SmallEtaleStagesEssSurj (P : SmallEtaleSheafProperty B A) : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B c.pt hX) A, P (B.obj c.pt hX) F →
    ∃ (i : I)
      (Fi : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A),
      P (Dg.obj (op i)) Fi ∧
        Nonempty ((smallEtaleStageProjection B A Dg c hX i).obj Fi ≅ F)
```

Clause (2) of Tag 0GL2 for finite locally constant abelian sheaves, and clause (3) for locally constant sheaves of `Λ`-modules of finite type with `Λ : Type (u + 1)` (`AlgebraicGeometry.smallEtaleStagesEssSurj_isFiniteLocallyConstant_addCommGrpCat`, `AlgebraicGeometry.smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_moduleCat`). The stages are quasi-compact and quasi-separated with affine transition maps:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteLocallyConstantLimit/EssSurj.lean`, lines 59, 61, 63, 1090, 1092, 1094–1096, 1098–1099, 1119–1127, 1139–1149:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
-- ⋯
universe t v u
-- ⋯
namespace AlgebraicGeometry
-- ⋯
section Instances
-- ⋯
attribute [local instance high] Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE
-- ⋯
attribute [local instance] SmallEtale.isRightAdjointPushforward_type
  SmallEtale.isRightAdjointPushforward_addCommGrpCat
  SmallEtale.isRightAdjointPushforward_moduleCat_site
-- ⋯
variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)
-- ⋯
/-- **Essential surjectivity, clause (2) of Tag 0GL2.** For `X = lim X_i` as in clause (1), every
finite locally constant sheaf of abelian groups on `X_étale` is the inverse image of a finite
locally constant sheaf of abelian groups at some stage. -/
public theorem smallEtaleStagesEssSurj_isFiniteLocallyConstant_addCommGrpCat (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B AddCommGrpCat.{u + 1} Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B AddCommGrpCat.{u + 1}) := by
-- ⋯
/-- **Essential surjectivity, clause (3) of Tag 0GL2.** For `X = lim X_i` as in clause (1) and any
commutative ring `Λ`, every locally constant sheaf of `Λ`-modules of finite type on `X_étale` is
the inverse image of a locally constant sheaf of `Λ`-modules of finite type at some stage. No
Noetherian hypothesis on `Λ` is needed. -/
public theorem smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_moduleCat
    (Λ : Type (u + 1)) [CommRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
      (isFiniteTypeLocallyConstantSmallEtaleSheaf.{u + 1} B Λ) := by
```

The same two conditions for a coefficient ring `Λ : Type` through a ring isomorphism `φ : Λ₀ ≃+* Λ` with `Λ₀ : Type (u + 1)`, and the form of 0GLI over an affine base on which `N` is invertible, whose proof spreads `f` out with the stage form of the theorem above and descends `F` and the relation `N • 𝟙 F = 0` to a stage with these two results (lines 267–295 of the file):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmoothProperHigherDirectImageLocallyConstantReduction.lean`, lines 64, 66, 68, 70, 72–73, 75, 110–111, 113, 115–122, 134–143, 148, 150, 152, 154, 156–157, 343, 345, 466–480:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
-- ⋯
universe u r
-- ⋯
namespace AlgebraicGeometry
-- ⋯
variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ]
-- ⋯
attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse
-- ⋯
variable {Λ₀ : Type (u + 1)} [CommRing Λ₀] (φ : Λ₀ ≃+* Λ)
-- ⋯
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)
-- ⋯
include φ
-- ⋯
/-- **Stacks 0GL2, clause (3), essential surjectivity, along a ring isomorphism.** -/
theorem smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_of_ringEquiv (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (SmallEtale.topology B Y.obj Y.property) F) := by
-- ⋯
omit [Nonempty I] in
/-- **Stacks 0GL2, clause (3), faithfulness, along a ring isomorphism.** -/
theorem smallEtaleStagesFaithful_isFiniteTypeLocallyConstant_of_ringEquiv [IsNoetherianRing Λ₀]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (SmallEtale.topology B Y.obj Y.property) F) :=
-- ⋯
end AlgebraicGeometry
-- ⋯
open AlgebraicGeometry Stacks.ConstantSheaf
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
-- ⋯
attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse smallEtaleHasSheafifyModuleMax
-- ⋯
section Affine
-- ⋯
variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
-- ⋯
/-- **Tag 0GLI over an affine base on which `N` is invertible, for a sheaf killed by `N`.** Let
`S` be affine, `f : X ⟶ S` smooth and proper, `N > 0` invertible on `S` and `F` a finite type,
locally constant sheaf of `Λ`-modules on `X` killed by `N`. Then every `Rᵠ f_* F` is finite type
and locally constant.

`S` is the limit of the spectra `S_t` of the finitely generated subrings of `Γ(S, ⊤)`; `f` is the
base change of a proper smooth `f_t` (Stacks 01ZM, 081F, 0C0C), and the stages may be taken to
contain an inverse of `N`, so that `N` is invertible on the Noetherian `S_t`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_isAffine (N : ℕ) (hN : 0 < N)
    {X S : B.Scheme} [IsAffine S.obj] (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
    (hunit : IsUnit ((N : ℕ) : Γ(S.obj, ⊤))) (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.obj.smallEtaleTopology Λ F)
    (hNF : N • 𝟙 F = 0) (q : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} S.obj.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) := by
```

### B.11 Raising the coefficient universe of abelian étale cohomology; module and abelian cohomology

On any site, under the stated hypotheses, the cohomology of an abelian sheaf equals that of its coefficient-universe lift (`Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`):

`StacksFrontier/CategoryTheory/Sites/Cohomology/CoefficientUniverseLift.lean`, lines 56, 58, 60, 62, 278–290:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
-- ⋯
universe u v w t z
-- ⋯
namespace Stacks.Cohomology.CoefficientLift
-- ⋯
section Transfer
-- ⋯
/-- Raising the coefficient universe of an abelian sheaf does not change its cohomology: the
additive equivalence induced by `CategoryTheory.Functor.mapExtAddHom` of the universe lift, read
through the identification `constantSheafUliftIso` of the two constant sheaves on `ULift ℤ`. -/
public noncomputable def sheafHUliftAddEquiv
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{v}] [HasSheafify J Ab.{max v t}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v}]
    [(sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).PreservesInjectiveObjects]
    [EnoughInjectives (Sheaf J Ab.{v})]
    [HasExt.{w} (Sheaf J Ab.{v})] [HasExt.{z} (Sheaf J Ab.{max v t})]
    (F : Sheaf J Ab.{v}) (n : ℕ) :
    Sheaf.H.{w} F n ≃+
      Sheaf.H.{z} ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).obj F) n := by
```

On Mathlib's small étale site of `X : Scheme.{u}`, from `AddCommGrpCat.{u}` to `AddCommGrpCat.{u + 1}` (`AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`), with the result that supplies the hypotheses (`AlgebraicGeometry.etaleUlift_properties`):

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleCoefficientLift.lean`, lines 70–71, 73, 75, 102–108, 128, 130, 172–180:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Cohomology.CoefficientLift
-- ⋯
universe u v t
-- ⋯
namespace AlgebraicGeometry
-- ⋯
/-- Universe lifting of abelian groups on the small étale site of a `u`-scheme is compatible with
sheafification and preserves injective objects, once `u ≤ v`.  The small dense subsite is a
small model of the affine étale site. -/
public lemma etaleUlift_properties (X : Scheme.{u}) [UnivLE.{u, v}] :
    X.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v} ∧
    (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{t, v}).PreservesInjectiveObjects := by
-- ⋯
section
-- ⋯
variable (X : Scheme.{u})
-- ⋯
/-- **The coefficient universe of étale cohomology can be raised freely.**  For an abelian sheaf
`F` on the small étale site of `X` with values at the morphism universe of the site, the
cohomology of `F` and the cohomology of its universe lift to the object universe of the site
agree in every degree. -/
public def smallEtaleSheafHUliftAddEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u, u} F n ≃+
      Sheaf.H.{u + 1, u + 1} ((sheafCompose X.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F) n :=
```

Higher direct images along a continuous functor of sites commute with the universe lift, and on the small étale site the lift from `u` to `u + 1` preserves injective objects (`Stacks.Sheaves.UniverseLift.rightDerivedSheafPushforwardContinuousULiftIso`, `Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_smallEtale`):

`StacksFrontier/CategoryTheory/Sites/UniverseLiftDerived.lean`, lines 49, 51, 74, 107, 109–110, 119–133, 187, 189, 191–194:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
-- ⋯
universe z s t v₁ v₂ u₁ u₂ u
-- ⋯
namespace Stacks.Sheaves.UniverseLift
-- ⋯
section Pushforward
-- ⋯
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D) [F.IsContinuous J K]
-- ⋯
variable [HasSheafify K AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{max t s}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{t}] [K.WEqualsLocallyBijective AddCommGrpCat.{max t s}]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{t})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{max t s})]
  [(uliftSheafFunctor.{s, t} K).PreservesInjectiveObjects]

/-- **The higher direct images along a continuous functor of sites commute with the universe
lift**: `Rᵠ F_*` of the lift of an abelian sheaf is the lift of `Rᵠ F_*`. -/
def rightDerivedSheafPushforwardContinuousULiftIso (q : ℕ) :
    (F.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived q ⋙
        uliftSheafFunctor.{s, t} J ≅
      uliftSheafFunctor.{s, t} K ⋙
        (F.sheafPushforwardContinuous AddCommGrpCat.{max t s} J K).rightDerived q :=
-- ⋯
section SmallEtale
-- ⋯
variable (X : AlgebraicGeometry.Scheme.{u})
-- ⋯
/-- **On the small étale site of a scheme, the universe lift of abelian sheaves from `u` to
`u + 1` preserves injective objects.** -/
instance preservesInjectiveObjects_uliftSheafFunctor_smallEtale :
    (uliftSheafFunctor.{u + 1, u} X.smallEtaleTopology).PreservesInjectiveObjects :=
```

Stacks 03FD: for a sheaf of rings `R` on a small category, the derived sections of `R`-module sheaves agree with those of the underlying abelian sheaves (`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`). It is stated for `SheafOfModules` on a `SmallCategory`, and as the existence of the comparison:

`StacksFrontier/CategoryTheory/Sites/GlobalSections/ModuleCohomologyComparison.lean`, lines 106, 108, 110, 717, 761, 1083–1105:

```lean
open CategoryTheory Opposite Limits
-- ⋯
namespace ModuleSheafCohomology
-- ⋯
open CategoryTheory.Abelian
-- ⋯
universe u v u'
-- ⋯
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
-- ⋯
/-- **Stacks 03FD.** For a sheaf of rings `R` on a site, deriving sections in the category of
`R`-module sheaves and then forgetting to abelian groups gives the same cohomology as first
forgetting to an abelian sheaf and deriving there. The comparison is natural in the module
sheaf, holds globally and over every object of the site, and is compatible in degree zero with
the canonical maps to right-derived functors. -/
@[stacks 03FD, stacks 03F2 "the degree one case", sga "4 V 3.5"]
public theorem moduleSheafCohomologyIsoUnderlying (R : Sheaf J RingCat.{u}) :
    ∃ eSite : ∀ i : ℕ,
        (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).rightDerived i ≅
          SheafOfModules.toSheaf.{u} R ⋙ (Sheaf.Γ J Ab.{u}).rightDerived i,
      (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).toRightDerivedZero ≫
          (eSite 0).hom =
        Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
          (Sheaf.Γ J Ab.{u}).toRightDerivedZero ∧
      ∀ U : C,
        ∃ eU : ∀ i : ℕ,
            (SheafOfModules.toSheaf.{u} R ⋙
                (sheafSections J Ab.{u}).obj (op U)).rightDerived i ≅
              SheafOfModules.toSheaf.{u} R ⋙
                ((sheafSections J Ab.{u}).obj (op U)).rightDerived i,
          (SheafOfModules.toSheaf.{u} R ⋙
                (sheafSections J Ab.{u}).obj (op U)).toRightDerivedZero ≫
              (eU 0).hom =
```

### B.12 The composition rule for Stacks' cohomology maps along morphisms with coefficient maps (an input to bridge B2)

The map `etaleCohomologyMapTo k w p : Sheaf.H A p →+ Sheaf.H B p` for `k : Y ⟶ X` and `w : k⁻¹A ⟶ B` (`Stacks.EtaleCohomology.etaleCohomologyMapTo`), and its composition rule for `k = k₁ ≫ k₂` (`Stacks.EtaleCohomology.etaleCohomologyMapTo_comp`). Both modules lie in the nine-root closure of Section 7.1 of the audit note:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean`, lines 192–193, 195, 197, 201, 203–221:

```lean
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe v u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
section MapTo
-- ⋯
variable {X Y : Scheme.{u}} (k : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The map on étale cohomology attached to a morphism of schemes and a map of sheaves.** Given
`k : Y ⟶ X`, an abelian sheaf `A` on the small étale site of `X`, one `B` on that of `Y` and a map
`w : k^{-1}A ⟶ B`, this is restriction along `k` followed by the map induced on cohomology by `w`.

Both ingredients of the cohomology cocone of [Stacks, Tag 09YQ] are of this shape: a leg is the
case `k = f_i` and `w = ι_i`, and a diagram map is the case `k = f_{ji}` and `w` the transition of
the system. Stating the naturality of the construction once, here, is what lets the dimension
shift treat the two uniformly. -/
def etaleCohomologyMapTo {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ B) (p : ℕ) :
    Sheaf.H.{u + 1, u + 1} A p →+ Sheaf.H.{u + 1, u + 1} B p :=
  (Sheaf.H.map w p).comp (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A p)
```
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtalePresentedSystem.lean`, lines 101–102, 104, 106, 108, 110–131:

```lean
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
-- ⋯
universe v u
-- ⋯
namespace Stacks.EtaleCohomology
-- ⋯
section MapToComp
-- ⋯
variable {X Y Z : Scheme.{u}}
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The composition law for the cohomology map of a morphism together with a map of sheaves.**
-/
theorem etaleCohomologyMapTo_comp (k₁ : Z ⟶ Y) (k₂ : Y ⟶ X) (k : Z ⟶ X) (hk : k = k₁ ≫ k₂)
    {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {C : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w₂ : (etaleAbelianInverseImage.{u, u + 1} k₂).obj A ⟶ B)
    (w₁ : (etaleAbelianInverseImage.{u, u + 1} k₁).obj B ⟶ C)
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ C)
    (hw : (etaleAbelianInverseImageCompIso'.{u, u + 1} k₁ k₂ k hk).hom.app A ≫
        (etaleAbelianInverseImage.{u, u + 1} k₁).map w₂ ≫ w₁ = w)
    (p : ℕ) (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k₁ w₁ p (etaleCohomologyMapTo k₂ w₂ p x) =
      etaleCohomologyMapTo k w p x := by
```

## C. FAG at `a25955c`

Paths are relative to the repository root. The coefficient ring is `Λ : Type (u + 1)`
throughout, and the sheaves are in `ModuleCat.{u + 1} Λ` unless stated otherwise. The
notations `(f)_*[…]`, `(f)^*[…]`, `R(…)` and `R+(…)` are FAG's direct image, inverse
image, and right derived direct image on `D` and on `D⁺`.

### C.1 Specialization for a smooth proper morphism (SGA 4 XVI 2.1–2.2)

`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_homology_lowerStar_of_smooth_of_isProper`
(strictly henselian base),
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper`
(any base, at the strict localization of a geometric point) and
`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`
(base of finite type over a field):

`WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/SmoothProperLocallyConstant.lean`, lines 49, 51, 53, 55, 57, 59, 61, 153–162, 180–189, 226–233:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
theorem Etale.isIso_globalSectionsUpperStarMap_homology_lowerStar_of_smooth_of_isProper
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R)) {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [Smooth π] [IsProper π] (N : ℕ) (hN₀ : N ≠ 0) (hN : (N : Λ) = 0)
    (hNR : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F] (q : ℤ) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        (R+((π)_*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
-- ⋯
theorem Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsProper f] (N : ℕ) (hN₀ : N ≠ 0)
    (hN : (N : Λ) = 0) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s) (q : ℤ) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((strictLocalizationToBase s)^*[ModuleCat.{u + 1} Λ].obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((f)_*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) := by
-- ⋯
theorem Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [Smooth f] [IsProper f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] (q : ℤ) :
    IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
```

A constant sheaf is locally constant: the instance
`AlgebraicGeometry.Etale.isLocallyConstantSheaf_constantSheaf`
(`WeilConjectures/ConstructibleSheaf/DenseOpenUnit.lean:227`).

### C.2 Proper and smooth base change

`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` and
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`:

`WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Proper.lean`, lines 76, 78, 80, 82, 84, 86, 88–89, 145–148, 168–170:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
-- ⋯
theorem Etale.isIso_baseChange_of_isProper [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : Etale.DerivedCategory.Plus.torsionHomology X K) :
    IsIso ((Etale.baseChange Ab.{u + 1} sq.toCommSq).app K) := by
-- ⋯
theorem Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ) [IsProper f]
    (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
```

`AlgebraicGeometry.Etale.isIso_baseChange_of_smooth`. Its section variables include
`[QuasiCompact f] [QuasiSeparated f]` (line 55), and the theorem adds `[Smooth g]` and
the hypothesis `hK : orderInvertibleOnHomology f K`:

`WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Smooth.lean`, lines 41, 43, 45, 47, 49, 51, 53–55, 58–61:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits MonoidalCategory Abelian
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [QuasiCompact f] [QuasiSeparated f]
-- ⋯
theorem Etale.isIso_baseChange_of_smooth [Smooth g] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : Etale.DerivedCategory.Plus.orderInvertibleOnHomology f K) :
    IsIso ((Etale.baseChange Ab.{u + 1} sq.toCommSq).app K) := by
```

### C.3 Finiteness for a proper morphism (SGA 4 XIV 1.2)

`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper`
and `AlgebraicGeometry.Etale.isIso_homology_derivedBaseChangeMapPlus_of_isProper`:

`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Proper.lean`, lines 38, 40, 42, 44, 46, 48, 50, 52, 54–55, 179–187, 205–224:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Etale
-- ⋯
open _root_.DerivedCategory
-- ⋯
variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
-- ⋯
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f]
    (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)))) ∧
    ∀ q : ℤ, (2 * d : ℤ) < q → IsZero ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) :=
-- ⋯
theorem isIso_homology_derivedBaseChangeMapPlus_of_isProper {X S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (f : X ⟶ S) [IsProper f]
    (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (q : ℤ),
      IsIso ((Plus.homologyFunctor _ q).map ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f s).toCommSq).app ((Plus.singleFunctor _ 0).obj F))) ∧
      IsFiniteSheaf ((Plus.homologyFunctor _ q).obj
        ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
          (((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
            ((Plus.singleFunctor _ 0).obj F)))) ∧
      ((2 * d : ℤ) < q → IsZero ((Plus.homologyFunctor _ q).obj
        ((pullback.snd f s)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
          (((pullback.fst f s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
            ((Plus.singleFunctor _ 0).obj F)))))) ∧
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)))) ∧
    ∀ q : ℤ, (2 * d : ℤ) < q → IsZero ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) := by
```

### C.4 Tag 09YQ: cohomology of a limit

The restriction map `AlgebraicGeometry.Etale.cohomologyRestrictOver` and the two halves of
the limit theorem, `AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`
and `AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_zero_of_isLimit`. Neither
requires torsion: the module documentation (lines 13–16) says that for `Λ = ℤ` these are
abelian étale sheaves and that no torsion hypothesis is needed.

`WeilConjectures/AlgebraicGeometry/Sites/CohomologyLimit.lean`, lines 39, 41, 43, 45, 47, 52–60, 166–170, 172, 178–183, 271–276:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite Abelian
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}}
-- ⋯
noncomputable def cohomologyRestrictOver {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ pZ = pY) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    Ext (SemiSimplicialObject.constSheaf Z.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pZ).obj F) q →+
      Ext (SemiSimplicialObject.constSheaf Y.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F) q :=
  (Ext.mk₀ ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm).inv.app F)).postcomp _
      (add_zero q) |>.comp (Etale.cohomologyRestrict Λ f _ q)
-- ⋯
variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
  (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
  (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
-- ⋯
include hc
-- ⋯
theorem exists_cohomologyRestrictOver_eq_of_isLimit (q : ℕ)
    (x : Ext (SemiSimplicialObject.constSheaf c.pt.left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) c.pt.hom).obj F) q) :
    ∃ (i : I) (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q),
      cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = x := by
-- ⋯
theorem exists_cohomologyRestrictOver_eq_zero_of_isLimit (q : ℕ) (i : I)
    (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q)
    (hy : cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = 0) :
    ∃ (j : I) (φ : j ⟶ i),
      cohomologyRestrictOver Λ (D.obj j).hom (D.obj i).hom (D.map φ).left (Over.w _) F q y = 0 := by
```

### C.5 Generic constructibility and base change for an open immersion over a field-base (a form of SGA 4½, Th. finitude 1.9)

The property `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn`: over a subset `U` of the base, for every noetherian `T` with a morphism `t : T ⟶ S` whose image lies in `U` and all cartesian squares over it, the derived direct image of the pulled-back sheaf is bounded constructible and the derived exchange map is an isomorphism:

`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Deligne/Defs.lean`, lines 21, 23, 25, 27, 29, 31, 33, 35, 56–65:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
def HasConstructibleDirectImageBaseChangeOn {S X Y : Scheme.{u}} (fY : Y ⟶ S) (j : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Set S) : Prop :=
  ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S), Set.range t ⊆ U →
    ∀ (YT XT : Scheme.{u}) (g : YT ⟶ Y) (fT : YT ⟶ T) (g' : XT ⟶ X) (jT : XT ⟶ YT),
      IsPullback g fT fY t → ∀ sq : IsPullback g' jT j g,
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
          ((R((jT)_*[ModuleCat.{u + 1} Λ])).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))
```

The exchange map `AlgebraicGeometry.Etale.derivedBaseChangeMap`, `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`:

`WeilConjectures/SixFunctors/BaseChange/DerivedUnbounded.lean`, lines 64, 66, 68, 70, 72, 74, 76–78, 80, 123–124:

```lean
@[expose] public section
-- ⋯
universe u' u
-- ⋯
open CategoryTheory
-- ⋯
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry
-- ⋯
namespace Etale
-- ⋯
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]
-- ⋯
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
-- ⋯
noncomputable def derivedBaseChangeMap (sq : CommSq g' f' f g) :
    R((f)_*[A]) ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ R((f')_*[A]) :=
```

`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible` (bounded for the canonical t-structure, with constructible homology sheaves):

`WeilConjectures/CategoryTheory/DerivedCategory/Constructible.lean`, lines 68, 70, 72, 74, 76, 78–81, 83, 85, 89–92, 96, 100–102:

```lean
@[expose] public section
-- ⋯
universe u' u
-- ⋯
open CategoryTheory Limits ZeroObject
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
-- ⋯
variable (X : Scheme.{u})
-- ⋯
section ConstructibleHomology
-- ⋯
noncomputable def Etale.DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ n : ℤ, IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj M)
-- ⋯
section BoundedConstructible
-- ⋯
noncomputable def Etale.DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.TStructure.t.bounded ⊓ Etale.DerivedCategory.constructibleHomology A X
```

`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf` and `AlgebraicGeometry.Scheme.IsConstructibleSheaf` (finite locally constant on the strata of one finite stratification):

`WeilConjectures/ConstructibleSheaf/Defs.lean`, lines 92, 94, 96, 98, 100, 102, 218, 220–223, 234–235, 292, 294–297, 343–345:

```lean
@[expose] public section
-- ⋯
universe u u'
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
noncomputable section
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {X Y : Scheme.{u}}
-- ⋯
section FiniteLocallyConstant
-- ⋯
variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
-- ⋯
class IsFiniteLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology A) : Prop
    extends IsLocallyConstantSheaf F, IsFiniteSheaf F
-- ⋯
section Constructible
-- ⋯
variable {A : Type u'} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
-- ⋯
class IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology A) : Prop where
  exists_stratification : ∃ S : Stratification X, ∀ i : Fin S.n,
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj F)
```

`AlgebraicGeometry.HasInvertibleExponent`:

`WeilConjectures/AlgebraicGeometry/InvertibleExponent.lean`, lines 30, 32, 34, 42–44:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
namespace AlgebraicGeometry
-- ⋯
class HasInvertibleExponent (Λ : Type*) [CommRing Λ] (X : Scheme.{u}) : Prop where
  /-- Some positive integer annihilating `Λ` is a unit in `Γ(X, ⊤)`. -/
  exists_isUnit_natCast : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0 ∧ IsUnit (n : Γ(X, ⊤))
```

The theorem `AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn` and its case `S = Spec k`, `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field`. The section variable `[Finite Λ]` (line 327) applies to both. The base `S` is integral and of finite type over a field `k`, and the morphism is an open immersion `j`:

`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Deligne.lean`, lines 57, 59, 61, 63, 65, 67, 69, 327, 410–416, 446–452:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
-- ⋯
theorem exists_hasConstructibleDirectImageBaseChangeOn {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      HasConstructibleDirectImageBaseChangeOn Λ fY j F U :=
-- ⋯
theorem boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field {k : Type u}
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (j : X ⟶ Y)
    [IsOpenImmersion j] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
```

### C.6 Étale sheaves on the spectrum of a field and discrete Galois modules; Galois automorphisms of a geometric fibre

`AlgebraicGeometry.Scheme.galoisPoint`, `galoisPointAct`, `isGaloisPoint_galoisPoint`, `etaleSheafEquivDiscreteModule` and `sheafHAddEquivGaloisH`, for a field `K` and a separable closure `Ω` (`[IsSepClosed Ω]` from line 93, `[Algebra.IsSeparable K Ω]` from line 163). They concern abelian étale sheaves on `Spec K` itself:

`WeilConjectures/AlgebraicGeometry/Sites/GaloisModule.lean`, lines 53, 55, 57, 59, 61, 64–65, 93, 97–98, 128, 163, 372–373, 386–389, 400–404:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω]
-- ⋯
noncomputable def specAlgebraMap : Spec (.of Ω) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ω))
-- ⋯
variable [IsSepClosed Ω]
-- ⋯
noncomputable def galoisPoint : (Spec (.of K)).smallEtaleTopology.Point.{u + 1} :=
  (pointSmallEtale (specAlgebraMap K Ω)).ulift.{u + 1}
-- ⋯
noncomputable def galoisPointAct : Gal(Ω/K) →* End (galoisPoint K Ω).fiber where
-- ⋯
variable [Algebra.IsSeparable K Ω]
-- ⋯
theorem isGaloisPoint_galoisPoint :
    (galoisPoint K Ω).IsGaloisPoint.{u + 1} (galoisPointAct K Ω) where
-- ⋯
noncomputable def etaleSheafEquivDiscreteModule :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      DiscreteModule.{u + 1} Gal(Ω/K) :=
  (isGaloisPoint_galoisPoint K Ω).equivalence
-- ⋯
noncomputable def sheafHAddEquivGaloisH
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (Sheaf.H F n : Type (u + 1)) ≃+
      DiscreteModule.H Gal(Ω/K) ((etaleSheafEquivDiscreteModule K Ω).functor.obj F) n :=
  (isGaloisPoint_galoisPoint K Ω).sheafHAddEquiv F n
```

The geometric fibre `X₀ ×_{Spec k} Spec k̄` of a scheme over a field `k` (`AlgebraicGeometry.Scheme.Hom.geometricFiber`), and its Galois endomorphisms `𝟙 × Spec σ` (`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap`), for any field `k` and its algebraic closure `k̄ = AlgebraicClosure k`:

`WeilConjectures/AlgebraicGeometry/GeometricFrobenius.lean`, lines 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124–127, 224, 335, 341–342:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
noncomputable section
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open FiniteField Scheme
-- ⋯
section AlgebraicClosure
-- ⋯
variable {k : Type u} [Field k]
-- ⋯
namespace Scheme.Hom
-- ⋯
variable {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
-- ⋯
/-- The geometric fiber `X := X₀ ×_{Spec k} Spec k̄` of a scheme `X₀` over a field `k`
with structure morphism `f : X₀ ⟶ Spec k`. -/
def geometricFiber : Scheme.{u} :=
  pullback f (Scheme.specAlgebraicClosure k).hom
-- ⋯
variable {f} {Y₀ Z₀ : Scheme.{u}} {g : Y₀ ⟶ Spec (.of k)} {e : Z₀ ⟶ Spec (.of k)}
-- ⋯
variable (g) in
-- ⋯
def geometricFiberGaloisMap (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) :
    g.geometricFiber ⟶ g.geometricFiber :=
```

The same maps as automorphisms, for `σ ∈ Gal(k̄/k)` (`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisIso`). The uses of these maps that we found concern Picard groups, group laws, fundamental groups and `H¹` of curves (`AlgebraicGeometry/Picard/GaloisTwist.lean`, `AbelianVariety/GaloisGroupLaw.lean`, `FundamentalGroup/Frobenius.lean`, `FundamentalGroup/CurveDualTateModule.lean`, `EtaleCohomology/Purity/RealSheaves/Jacobian.lean` and `JacobianKummer.lean`). None of them assembles an action on `Hⁿ(X₀ ×_k Spec k̄, M)` for every `n`:

`WeilConjectures/AlgebraicGeometry/FundamentalGroup/CurveDualTateModule.lean`, lines 41, 43, 45, 256, 258, 260, 262–265:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits PreGaloisCategory
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open MonoidalCategory CartesianMonoidalCategory MonObj
-- ⋯
variable {K : Type u} [Field K]
-- ⋯
/-- The Galois action `𝟙 × Spec σ` of `σ ∈ Gal(K̄/K)` on the geometric fibre of a `K`-scheme, as
an automorphism. -/
noncomputable def Scheme.Hom.geometricFiberGaloisIso {Y₀ : Scheme.{u}} (g : Y₀ ⟶ Spec (.of K))
    (σ : Gal(AlgebraicClosure K/K)) : g.geometricFiber ≅ g.geometricFiber where
```

### C.7 Inertia groups, finite étale covers and specialization maps (inputs to bridge F5)

`AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut_hom_app_eq_of_mem_inertia`: for a domain `R` with fraction field `K`, a morphism `a : Spec R ⟶ Y` to a connected scheme, a separably closed Galois extension `Ω/K` and a maximal ideal `Q` of the integral closure of `R` in `Ω`, every element of the inertia group of `Q` acts trivially on the geometric fibre at `Spec Ω ⟶ Spec K ⟶ Y` of every finite étale `Y`-scheme:

`WeilConjectures/AlgebraicGeometry/FundamentalGroup/DecompositionGroup.lean`, lines 28, 30, 32, 34, 36–38, 73–77:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits PreGaloisCategory
-- ⋯
namespace AlgebraicGeometry.Scheme.FiniteEtale
-- ⋯
variable {Y : Scheme.{u}} {R K Ω : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsSepClosed Ω] (a : Spec (.of R) ⟶ Y)
-- ⋯
theorem galoisToAut_hom_app_eq_of_mem_inertia [ConnectedSpace Y]
    (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] {σ : Ω ≃ₐ[K] Ω}
    (hσ : σ ∈ Q.inertia (Ω ≃ₐ[K] Ω)) (P : Y.FiniteEtale)
    (t : (fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a))).obj P) :
    (galoisToAut _ σ).asIso.hom.app P t = t := by
```

The ring of inertia invariants `Ideal.inertiaInvariants` (`B_Q^{I_Q}` for the integral closure `B` of `R` in `Ω`), which is strictly henselian. For a Dedekind domain `R` and a maximal ideal `m` under `Q`, its localization away from a nonzero element of `m` is the fixed field of `I_Q`; this theorem omits the section's hypothesis that the residue field at `m` is perfect (line 546). If that residue field is perfect, the ring is ind-étale over `R`:

`WeilConjectures/RingTheory/InertiaIndEtale.lean`, lines 39, 41–42, 44, 46, 48–50, 54–58, 70–72, 381, 383–386, 546–553, 590, 592, 594–597, 599, 602:

```lean
@[expose] public section
-- ⋯
open IsLocalRing
open scoped Pointwise
-- ⋯
namespace Ideal
-- ⋯
section Invariants
-- ⋯
variable {R : Type*} (K : Type*) {Ω : Type*} [CommRing R] [Field K] [Field Ω] [Algebra R K]
  [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
-- ⋯
noncomputable def inertiaInvariants : Subalgebra R (Localization.AtPrime Q) :=
  letI := inertiaAtPrimeAction Q Gal(Ω/K)
  { FixedPoints.subring (Localization.AtPrime Q) (Q.inertia Gal(Ω/K)) with
    algebraMap_mem' := fun r g ↦
      atPrimeMap_algebraMap_base Q g.1 (inertia_le_stabilizer Q g.2) r }
-- ⋯
theorem isStrictlyHenselianLocalRing_inertiaInvariants [IsSepClosed Ω]
    [Algebra.IsAlgebraic R Ω] (hR : Function.Injective (algebraMap R Ω)) :
    IsStrictlyHenselianLocalRing (inertiaInvariants K Q) := by
-- ⋯
section IndEtale
-- ⋯
variable {R : Type*} (K : Type*) {Ω : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Field Ω] [Algebra R K] [IsFractionRing R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] (m : Ideal R) [m.IsMaximal] [PerfectField m.ResidueField]
  (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] [Q.LiesOver m]
-- ⋯
omit [PerfectField m.ResidueField] in
include m in
/-- **The punctured spectrum of `B_Q^{I_Q}`.** For `0 ≠ ϖ ∈ m`, the localization `A[1/ϖ]` of
`A = B_Q^{I_Q}` is the fixed field `Ω^{I_Q}` of the inertia group.
(blueprint `lemma-boundary-stalk--1`) -/
theorem isLocalization_away_inertiaInvariants {ϖ : R} (hϖ : ϖ ∈ m) (hϖ0 : ϖ ≠ 0) :
    IsLocalization.Away (algebraMap R (inertiaInvariants K Q) ϖ)
      (IntermediateField.fixedField (Q.inertia Gal(Ω/K))) := by
-- ⋯
section IndEtaleUniverse
-- ⋯
universe u
-- ⋯
variable {R : Type u} (K : Type*) {Ω : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Field Ω] [Algebra R K] [IsFractionRing R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] (m : Ideal R) [m.IsMaximal] [PerfectField m.ResidueField]
  (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] [Q.LiesOver m]
-- ⋯
include m in
-- ⋯
theorem indEtale_inertiaInvariants : Algebra.IndEtale R (inertiaInvariants K Q) := by
```

`AlgebraicGeometry.Scheme.exists_iso_uliftYoneda_of_isFiniteLocallyConstant`: a sheaf of sets on the small étale site that is constant on the members of an étale cover and has finite stalks is the sheaf of sections of a finite étale scheme:

`WeilConjectures/AlgebraicGeometry/FiniteLocallyConstantEtale.lean`, lines 57, 59, 61, 63, 65, 227–233:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {T : Scheme.{u}}
-- ⋯
theorem exists_iso_uliftYoneda_of_isFiniteLocallyConstant
    (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hE : (∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧ IsFiniteSheaf E) :
    ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : AlgebraicGeometry.Etale π),
      Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
```

`AlgebraicGeometry.Etale.stalkHom_comp_specializationStalk` and `AlgebraicGeometry.Etale.injective_specializationStalk`: for a strictly henselian local ring `A` with `a : Spec A ⟶ X`, a morphism `j : U ⟶ X` and a geometric point `η : Spec Ω ⟶ U` over `Spec Ω ⟶ Spec A ⟶ X`, the specialization map `specializationStalk : (j_* F)_{s̄} ⟶ F_η` from the stalk at the closed geometric point `s̄` intertwines the actions of compatible endomorphisms `τ` of `A` over `X` and `σ` of `Ω`. It is injective for a locally constant `F` when `j` is an open immersion, `X` is locally noetherian and the local rings of its étale `X`-schemes are domains. The module documentation (lines 30–33) draws the consequence that the image consists of invariants of the automorphisms of `Ω` that come from automorphisms of `A` inducing the identity on the residue field, that is, of the inertia group. That consequence is not stated as a separate theorem:

`WeilConjectures/ConstructibleSheaf/LowerStarSpecialization.lean`, lines 45, 47, 49, 51, 53, 221, 223, 225–228, 268–278, 310–313:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Etale
-- ⋯
section Specialization
-- ⋯
variable {X U : Scheme.{u}} (j : U ⟶ X) {A : Type u} [CommRing A]
  [IsStrictlyHenselianLocalRing A] (a : Spec (.of A) ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ι : CommRingCat.of A ⟶ CommRingCat.of Ω) (η : Spec (.of Ω) ⟶ U)
  (hη : η ≫ j = Spec.map ι ≫ a) {Λ : Type (u + 1)} [Ring Λ]
-- ⋯
theorem stalkHom_comp_specializationStalk (τ : A →+* A)
    (hτa : Spec.map (CommRingCat.ofHom τ) ≫ a = a)
    (τ' : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A)
    (hτ : closedGeometricPoint A ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom τ') ≫ closedGeometricPoint A) (σ : Ω →+* Ω)
    (hσι : ι ≫ CommRingCat.ofHom σ = CommRingCat.ofHom τ ≫ ι)
    (hση : Spec.map (CommRingCat.ofHom σ) ≫ η = η)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtaleHom _ τ' (comp_closedGeometricPoint_comp_eq a τ hτa τ' hτ)).sheafFiber.app
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ≫ specializationStalk j a ι η hη F =
      specializationStalk j a ι η hη F ≫ (pointSmallEtaleHom η σ hση).sheafFiber.app F := by
-- ⋯
theorem injective_specializationStalk [IsOpenImmersion j]
    (hX : ∀ (W : X.Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    [IsLocallyNoetherian X] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] : Function.Injective (specializationStalk j a ι η hη F) := by
```

`AlgebraicGeometry.Etale.galoisStalkMap_boundarySpecialization`: the same specialization map for an open immersion `j : U ⟶ C` into an integral scheme `C`, at the closed geometric point of `Spec (B_Q)`, where `B` is the integral closure in a separably closed Galois extension `Ω` of the function field `k(C)` of the ring of sections `Γ(C, W)` of an affine open `W`, and `Q` is a maximal ideal of `B`. Its image is fixed by the inertia group `Q.inertia`, acting on the stalk `F_η` at the generic geometric point `η : Spec Ω ⟶ U` (`genericGeometricPoint`, `AlgebraicGeometry/FundamentalGroup/ExtendOverInertia.lean:428`). Nothing is assumed of `C` beyond integrality, and nothing of `F`. The file is written for boundary points of curves over a finite field, but this part of it does not use that setting:

`WeilConjectures/EtaleCohomology/Purity/RealSheaves/BoundaryStalk.lean`, lines 46, 48, 50, 52, 54, 56, 58–62, 64–67, 78–83, 91–94, 108, 110, 112–113, 196–200:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme Scheme.FiniteEtale
-- ⋯
namespace Etale
-- ⋯
variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsIntegral C]
  [Nonempty U] {W : C.Opens} [Fact (IsAffineOpen W)] [Nonempty W]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal] {Λ : Type (u + 1)} [Ring Λ]
-- ⋯
/-- The geometric point `x̄ : Spec κ(B_Q) ⟶ Spec B_Q ⟶ C` over the boundary point. -/
noncomputable abbrev boundaryGeometricPoint :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime Q))) ⟶ C :=
  closedGeometricPoint (Localization.AtPrime Q) ≫ specAtPrime Fact.out Q
-- ⋯
variable {j} in
/-- The action of `σ ∈ Gal(Ω / k(C))` on the geometric generic stalk `F_η`. -/
noncomputable def galoisStalkMap (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (σ : Ω ≃ₐ[C.functionField] Ω) :
    (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F ⟶
      (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :=
-- ⋯
noncomputable def boundarySpecialization (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
      (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :=
-- ⋯
section Decomposition
-- ⋯
open scoped Pointwise
-- ⋯
variable {σ : Ω ≃ₐ[C.functionField] Ω}
  (hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[C.functionField] Ω) Q)
-- ⋯
theorem galoisStalkMap_boundarySpecialization (hσ' : σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω))
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (x : ToType ((pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F))) :
    galoisStalkMap F σ (boundarySpecialization j Q F x) = boundarySpecialization j Q F x := by
```

### C.8 Generic base change for a smooth source with finite locally constant coefficients (the smooth step of SGA 4½, Th. finitude 1.9, over a field-base)

The property `AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus` of a bounded below complex `K` and its relation to the property `HasConstructibleDirectImageBaseChangeOn` of C.5 for a sheaf placed in degree `0` (`hasConstructibleDirectImageBaseChangeOn_iff`):

`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Deligne/Plus.lean`, lines 35, 37, 39, 41, 43, 45, 47, 49–80, 91–98:

````lean
universe u
-- ⋯
open CategoryTheory Limits Pretriangulated
-- ⋯
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
/-- Over a subset `U` of `S`, the derived direct image of the bounded below complex `K` along
`j : X ⟶ Y`, for `Y` over `S` via `fY`, is bounded constructible and its formation commutes with
every base change from a noetherian scheme: for every noetherian `T`, every `t : T ⟶ S` with
image in `U` and all cartesian squares

```
  X_T --g'--> X
   |          |
  j_T         j
   ↓          ↓
  Y_T --g---> Y
   |          |
  f_T         fY
   ↓          ↓
   T ---t---> S
```

the direct image `Rj_{T,*}(g'^* K)` is bounded constructible and the derived base change map
`g^* Rj_* K ⟶ Rj_{T,*} g'^* K` on the bounded below derived categories is an isomorphism. For a
sheaf placed in degree `0` this is `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn`
(`AlgebraicGeometry.Etale.hasConstructibleDirectImageBaseChangeOn_iff`). -/
def HasDirectImageBaseChangeOnPlus {S X Y : Scheme.{u}} (fY : Y ⟶ S) (j : X ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (U : Set S) : Prop :=
  ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S), Set.range t ⊆ U →
    ∀ (YT XT : Scheme.{u}) (g : YT ⟶ Y) (fT : YT ⟶ T) (g' : XT ⟶ X) (jT : XT ⟶ YT),
      IsPullback g fT fY t → ∀ sq : IsPullback g' jT j g,
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
          (_root_.DerivedCategory.Plus.ι.obj
            ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
            (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) ∧
        IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)
-- ⋯
/-- The property `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn` of a sheaf is
the property `AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus` of the sheaf placed in
degree `0`. -/
theorem hasConstructibleDirectImageBaseChangeOn_iff {S X Y : Scheme.{u}} (fY : Y ⟶ S)
    (j : X ⟶ Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Set S) :
    HasConstructibleDirectImageBaseChangeOn Λ fY j F U ↔
      HasDirectImageBaseChangeOnPlus Λ fY j
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
````

The statement `AlgebraicGeometry.Etale.SmoothGenericDirectImage`. Here the base morphism is `fY = 𝟙 S` and the morphism `j` of `HasDirectImageBaseChangeOnPlus` is the smooth morphism `a` itself. So the conclusion says: for every noetherian `T` and every `t : T ⟶ S` with image in `U`, the derived direct image of `g'^* F` along the base change `a_T : X ×_S T ⟶ T` is bounded constructible, and the derived base change map `t^* Ra_* F ⟶ Ra_{T,*} g'^* F` is an isomorphism:

`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Deligne/Statement.lean`, lines 31, 33, 35, 37, 39, 41, 87, 104–116:

```lean
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
/-- **The smooth case**, the statement of `lemma-smooth-morphisms-locally-constant-sheaves` used by
the proof of `theorem-generic-constructibility-base-change-rj`: for a separated smooth morphism of
finite type `a : X ⟶ S` to an integral scheme of finite type over a field on which the exponent of
`Λ` is invertible, and a finite locally constant sheaf `F` on `X`, there is a nonempty open `U ⊆ S`
over which `Ra_* F` is bounded constructible and commutes with every base change from a
noetherian scheme. -/
def SmoothGenericDirectImage : Prop :=
  ∀ ⦃k : Type u⦄ [Field k] ⦃S X : Scheme.{u}⦄ [IsIntegral S] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [HasInvertibleExponent Λ S] (a : X ⟶ S)
    [Smooth a] [IsSeparated a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F],
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ (𝟙 S) a
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U
```

The theorem `AlgebraicGeometry.Etale.smoothGenericDirectImage`, for a finite coefficient ring `Λ` (section variable, line 327):

`WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Deligne.lean`, lines 59, 61, 63, 65, 67, 69, 327, 329–342:

```lean
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
-- ⋯
/-- A smooth source with finite locally constant coefficients.
(blueprint: lem-fin-smooth-generic-direct-image-finite-ring)

For a separated smooth morphism of finite type `a : X ⟶ S` to an integral scheme of finite type
over a field on which the exponent of `Λ` is invertible, and a finite locally constant sheaf `F`
on `X`, there is a nonempty open `U ⊆ S` over which `Ra_* F` is bounded constructible and
commutes with every base change from a noetherian scheme
(`AlgebraicGeometry.Etale.SmoothGenericDirectImage`).

This records the form of the node used by the induction for
`theorem-generic-constructibility-base-change-rj`: the blueprint asks for `𝔽_ℓ`-coefficients and
finite locally constant cohomology sheaves of `Rf_{U,*} L`, whereas this states bounded
constructibility (with base change) over any finite ring `Λ` whose exponent is invertible on `S`. -/
theorem smoothGenericDirectImage : SmoothGenericDirectImage Λ := by
```

The theorem from which FAG derives `smoothGenericDirectImage` (`Deligne.lean`, line 298): the same situation with coefficients `ULift (ZMod ℓ)` for a prime `ℓ ≠ char k`, whose conclusion adds that every cohomology sheaf of the direct image over `U` is finite locally constant, and states base change for the unbounded derived categories, `AlgebraicGeometry.Etale.exists_nonempty_open_smooth_directImage_lisse_baseChange`:

`WeilConjectures/AlgebraicGeometry/SmoothGenericDirectImage.lean`, lines 25, 27–28, 30, 81–150:

```lean
universe u
-- ⋯
open CategoryTheory Limits
open scoped CategoryTheory.Functor
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
/-- A finite locally constant prime-field sheaf on a separated smooth finite-type source
has bounded finite locally constant ordinary derived direct image on a nonempty base open,
where its canonical ordinary exchange is invertible for every Noetherian test scheme.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-asd-smooth-generic-direct-image.md`
(blueprint: lemma-smooth-morphisms-locally-constant-sheaves).

Proof:
1. The schemes are Noetherian by lemma-smooth-morphisms-locally-constant-sheaves--1. The locally
constant relative
   dimension (lemma-smooth-morphisms-locally-constant-sheaves) and quasi-compactness
   split X into finitely many open-and-closed pure-dimensional pieces. Compactify each
   by theorem-nagata-s-compactification-theorem--1.
2. On one piece put omega = f^times lambda and N = L^dual tensor omega.
   By proposition-exceptional-inverse-image-smooth-morphism, omega is a rank-one lisse sheaf shifted
   by 2d. Finite-free biduality gives L = RHom(N, omega): compute on trivializing etale
   neighborhoods and use lemma-weil-pbc-geometric-stalk-conservative. Thus N is bounded
   constructible.
3. lemma-internal-adjunction-two-exchange-formulas--1 identifies Rf_*L with RHom(Rf_!N, lambda).
   lemma-smooth-morphisms-locally-constant-sheaves makes C = Rf_!N bounded constructible.
   In each of its finitely many cohomological degrees, the stratum through the generic
   point contains a nonempty open. Intersect these opens and apply
   lemma-smooth-morphisms-locally-constant-sheaves to obtain bounded finite locally constant
   cohomology of the dual.
4. For every Noetherian T, proposition-exceptional-inverse-image-smooth-morphism--6 identifies the
pulled-back omega
   and N with those for f_T. Base-changed compactification and finite type make the
   ambient adjunction available (lemma-nagata-compactification-base-change and
   lemma-smooth-morphisms-locally-constant-sheaves--1). Compact-support exchange and
   lemma-smooth-morphisms-locally-constant-sheaves then give an isomorphism between the desired
   objects.
5. Identify this map with definition-derived-base-change-map--1: transpose the internal-adjunction
   pairing obtained from the ordinary counit f^*Rf_*L -> L and evaluation L tensor N ->
   omega. Compact exchange is natural for this pairing; exceptional exchange is the
   transpose of compact exchange followed by the exceptional counit. Pulling back these
   pairings therefore gives precisely the ordinary inverse-image square comparison
   followed by the pulled-back ordinary counit. Equality of adjunction transposes proves
   equality with the specified ordinary exchange, hence its invertibility.
6. Intersect the opens from all dimensions. Direct image and exchange on a finite
   disjoint union are finite products, which are exact in the abelian sheaf category.
   Take common bounds; finite sums of finite locally constant sheaves remain so.
   For empty X use the zero complex and the whole integral base as the open. -/
theorem exists_nonempty_open_smooth_directImage_lisse_baseChange
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    ∃ U : S.Opens, Nonempty U ∧
      ∀ (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
        IsPullback p fU f U.ι →
        (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        (∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
          ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
          (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
          (sq : IsPullback vX fT fU v),
          IsIso ((derivedBaseChangeMap
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sq.toCommSq).app
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))) := by
```

### C.9 Tag 03Q9 (stalks of higher direct images), strict henselization of a field, and the stalk of an étale sheaf on the spectrum of a field as a Galois representation

The restriction of a section of the cohomology presheaf `V ↦ H^q(V ×_S X, F|)` to a `T`-point (`cohomologyPresheafRestrict`) and its compatibility with composition:

`WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/StalkFormula.lean`, lines 41, 43, 45, 47, 49, 135, 137, 159, 161–171, 357–367:

```lean
universe u
-- ⋯
open CategoryTheory Limits Opposite Abelian
-- ⋯
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
section Restrict
-- ⋯
variable {X S : Scheme.{u}} (f : X ⟶ S)
-- ⋯
variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
-- ⋯
/-- The restriction of a section `Hᵠ(V ×_S X, F|)` of the cohomology presheaf to a `T`-point
`b` of `V` over `f`: a class `f^* Λ[V] ⟶ F[q]` is pulled back along `t : T ⟶ X` and evaluated
at the canonical section of `t^* f^* Λ[V]`. -/
noncomputable def cohomologyPresheafRestrict {T : Scheme.{u}} (t : T ⟶ X) (V : S.Etale)
    (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) :
    (Etale.higherDirectImagePresheaf Λ f q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V) →+
      Ext (SemiSimplicialObject.constSheaf T.smallEtaleTopology Λ)
        ((t)^*[ModuleCat.{u + 1} Λ].obj F) q :=
  ((t)^*[ModuleCat.{u + 1} Λ].mapExtPrecomp (freeSheafPullbackMap Λ f t V b hb) F q).comp
    (DerivedCategory.Plus.shiftedHomAddEquivExt _ _ q).toAddMonoidHom
-- ⋯
/-- `cohomologyPresheafRestrict_comp` with the composite morphisms given up to equality. -/
lemma cohomologyPresheafRestrict_comp' {T T' : Scheme.{u}} (t : T ⟶ X) (h : T' ⟶ T)
    (V : S.Etale) (b : T ⟶ V.left) (hb : b ≫ V.hom = t ≫ f) (t' : T' ⟶ X) (ht' : h ≫ t = t')
    (b' : T' ⟶ V.left) (hb' : h ≫ b = b')
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V)) :
    cohomologyPresheafRestrict Λ f F q t' V b' (by rw [← ht', ← hb', Category.assoc, hb,
        Category.assoc]) p =
      cohomologyRestrictOver Λ t' t h ht' F q (cohomologyPresheafRestrict Λ f F q t V b hb p) := by
  subst ht' hb'
  exact cohomologyPresheafRestrict_comp Λ f F q t h V b hb p
```

The comparison map `higherDirectImageStalkComparison` from the fibre at a geometric point `s` of that presheaf to `H^q(S_(s) ×_S X, F|)`, and its value on germs. Here `S_(s)` is the strict localization, `Scheme.strictLocalizationToBase s : S_(s) ⟶ S`:

`WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/StalkFormula.lean`, lines 41, 43, 45, 47, 49, 370, 372–373, 425, 444–466:

```lean
universe u
-- ⋯
open CategoryTheory Limits Opposite Abelian
-- ⋯
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
section Stalk
-- ⋯
variable {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)
-- ⋯
variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
-- ⋯
/-- The comparison map from the fibre at `s` of the cohomology presheaf `V ↦ Hᵠ(V ×_S X, F|)`
to the cohomology `Hᵠ(S_(s) ×_S X, F|)`: restriction along the points `S_(s) ×_S X ⟶ V`. -/
noncomputable def higherDirectImageStalkComparison :
    ((Scheme.pointSmallEtale s).presheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (Etale.higherDirectImagePresheaf Λ f q ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      AddCommGrpCat.of (Ext (SemiSimplicialObject.constSheaf
          (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj F) q) :=
  (Scheme.pointSmallEtale s).presheafFiberDesc
    (fun V v ↦ AddCommGrpCat.ofHom (cohomologyPresheafRestrict Λ f F q _ V
      (stalkPoint f s (Functor.elementsMk _ V v)) (stalkPoint_w f s (Functor.elementsMk _ V v))))
    (fun _ _ a v ↦ AddCommGrpCat.ext fun p ↦
      cohomologyPresheafRestrict_stalkPoint_map Λ f s F q a v p)

lemma toPresheafFiber_higherDirectImageStalkComparison (V : S.Etale)
    (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (p : (Etale.higherDirectImagePresheaf Λ f q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V)) :
    higherDirectImageStalkComparison Λ f s F q ((Scheme.pointSmallEtale s).toPresheafFiber V v
      (Etale.higherDirectImagePresheaf Λ f q ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) p) =
      cohomologyPresheafRestrict Λ f F q _ V (stalkPoint f s (Functor.elementsMk _ V v))
        (stalkPoint_w f s (Functor.elementsMk _ V v)) p :=
```

The theorem `AlgebraicGeometry.Etale.nonempty_geometricStalk_higherDirectImage_addEquiv` (tag 03Q9). Its proof shows that the comparison map is bijective (line 492, `suffices hΘ : Function.Bijective Θ`). The statement exports only the existence of an additive equivalence:

`WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/StalkFormula.lean`, lines 41, 43, 45, 47, 49, 471–485:

```lean
universe u
-- ⋯
open CategoryTheory Limits Opposite Abelian
-- ⋯
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
/-- **Strict-henselization stalk formula** (blueprint
`prop-weil-pbc-strict-henselization-stalk-formula`): for a quasi-compact quasi-separated
`f : X ⟶ S`, a sheaf `F` of `Λ`-modules on `X_ét` and a geometric point `s : Spec Ω ⟶ S`, the
geometric stalk of `R^q f_* F` at `s` is the étale cohomology `H^q(S_(s) ×_S X, F|)` of the base
change of `X` to the strict localization `S_(s)`. -/
@[stacks 03Q9]
theorem nonempty_geometricStalk_higherDirectImage_addEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty ((Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} Λ)).obj
        (Etale.higherDirectImage Λ f q F) ≃+
      Ext (SemiSimplicialObject.constSheaf
          (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj F) q) := by
```

The strict henselization of `Spec K` at a geometric point `Spec Ω ⟶ Spec K`: every element of `Ω` separable over `K` is a value of the evaluation map, the evaluation map is injective, the strict henselization is a field, and for `Ω` algebraic over `K` the morphism `Spec Ω ⟶ Spec K_(s)` is a universal homeomorphism:

`WeilConjectures/AlgebraicGeometry/Sites/StrictHenselizationField.lean`, lines 29, 31, 33, 35, 47–51, 62–68, 106–109, 116–121:

```lean
universe u
-- ⋯
open CategoryTheory Limits Opposite Polynomial
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {K Ω : Type u} [Field K] [Field Ω] [IsSepClosed Ω] [Algebra K Ω]
-- ⋯
/-- Every element of `Ω` which is separable over `K` is the value of an element of the strict
henselization of `Spec K` at `Spec Ω ⟶ Spec K`: the standard étale algebra of its minimal
polynomial is a pointed étale neighbourhood carrying a root with this value. -/
lemma exists_strictHenselizationEval_eq_of_isSeparable {x : Ω} (hx : IsSeparable K x) :
    ∃ a, strictHenselizationEval (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) a = x := by
-- ⋯
/-- The evaluation of the strict henselization of `Spec K` at the geometric point
`Spec Ω ⟶ Spec K` is injective. An element `c` of the ring `R` of a pointed étale
neighbourhood with value zero is killed by an element `g` with nonzero value, `R` being a
reduced artinian ring; and `g` becomes a unit on the neighbourhood `Spec R[1/g]`. -/
theorem strictHenselizationEval_injective_of_field :
    Function.Injective
      (strictHenselizationEval (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) := by
-- ⋯
/-- The strict henselization of `Spec K` at a geometric point `Spec Ω ⟶ Spec K` is a field: it
is local with maximal ideal the kernel of the (injective) evaluation. -/
theorem isField_strictHenselization_of_field :
    IsField (strictHenselization (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) := by
-- ⋯
/-- If `Ω` is separably closed and algebraic over `K`, the morphism `Spec Ω ⟶ Spec K_(s)` from
the geometric point `s : Spec Ω ⟶ Spec K` to the strict localization is a universal
homeomorphism: the strict henselization is a field over which `Ω` is purely inseparable. -/
theorem isUniversalHomeomorphism_spec_strictHenselizationEval [Algebra.IsAlgebraic K Ω] :
    IsUniversalHomeomorphism
      (Spec.map (strictHenselizationEval (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))) := by
```

Abelian étale sheaves on `Spec K` as discrete continuous representations of `Gal(Ks/K)`. The underlying group is the stalk at `Spec Ω ⟶ Spec K`, and `σ` acts on the germ at a lift `x` as the germ at `Spec τ ≫ x`, for any automorphism `τ` of `Ω` extending `σ`:

`WeilConjectures/AlgebraicGeometry/EtaleSheafDiscreteContinuousRep.lean`, lines 33, 35, 37, 39–40, 42–49, 51–52, 54–64, 66–85:

```lean
universe u
-- ⋯
open CategoryTheory Opposite
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks] [IsSepClosed Ks]
  [Algebra.IsSeparable K Ks]
-- ⋯
/-- Abelian étale sheaves on `Spec K` are equivalent to discrete continuous integral
representations of `Gal(Ks/K)`: the equivalence `etaleSheafEquivDiscreteModule` composed with
`DiscreteModule.discreteContinuousRepEquivalence`. -/
noncomputable def etaleSheafEquivDiscreteContinuousRep :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ Gal(Ks/K) :=
  (etaleSheafEquivDiscreteModule K Ks).trans
    (DiscreteModule.discreteContinuousRepEquivalence.{u + 1} Gal(Ks/K))
-- ⋯
variable (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra Ks Ω] [IsScalarTower K Ks Ω]
  [IsSepClosed Ω]
-- ⋯
/-- The underlying abelian group of the discrete representation attached to an abelian étale
sheaf on `Spec K` is its stalk at the geometric point `Spec Ω ⟶ Spec K`. -/
noncomputable def etaleSheafEquivDiscreteContinuousRepForgetIso :
    (etaleSheafEquivDiscreteContinuousRep K Ks).functor ⋙ ObjectProperty.ι _ ⋙
        Rep.RepToAction ℤ Gal(Ks/K) ⋙ Action.forget (ModuleCat.{u + 1} ℤ) Gal(Ks/K) ⋙
          forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  Functor.isoWhiskerLeft (etaleSheafEquivDiscreteModule K Ks).functor
      (DiscreteModule.toDiscreteContinuousRepCompForgetIso.{u + 1} Gal(Ks/K)) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl) ≪≫
    galoisPointSheafFiberIso K Ks Ω
-- ⋯
/-- Under `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRepForgetIso`, the
element `σ ∈ Gal(Ks/K)` acts on the germ of `z` at a lift `x` of the geometric point
`Spec Ω ⟶ Spec K` as the germ of `z` at `Spec τ ≫ x`, for any automorphism `τ` of `Ω`
extending `σ`. -/
lemma etaleSheafEquivDiscreteContinuousRepForgetIso_ρ
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (σ : Gal(Ks/K))
    (τ : Ω ≃ₐ[K] Ω)
    (hτ : (algebraMap Ks Ω).comp σ.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω))
    (X : (Spec (.of K)).Etale)
    (x x' : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
    (z : F.obj.obj (op X)) :
    (etaleSheafEquivDiscreteContinuousRepForgetIso K Ks Ω).hom.app F
        (((etaleSheafEquivDiscreteContinuousRep K Ks).functor.obj F).obj.ρ σ
          ((etaleSheafEquivDiscreteContinuousRepForgetIso K Ks Ω).inv.app F
            ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
              X x F.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z :=
  galoisPointSheafFiberIso_presheafFiberAct K Ks Ω F σ τ hτ X x x' hx z
```

Topological invariance of étale cohomology (tag 03SI) for abelian sheaves: the comparison map `cohomologyMap f F n : H^n(Y, F) →+ H^n(X, f^* F)` is bijective for a universal homeomorphism `f : X ⟶ Y`:

`WeilConjectures/SixFunctors/Etale/UpperLowerStar/TopologicalInvariance.lean`, lines 93, 95, 97, 99, 173, 175–176, 178–187, 214, 216, 218–224:

```lean
universe u' u
-- ⋯
open CategoryTheory Abelian
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
open Scheme
-- ⋯
section Cohomology
-- ⋯
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
-- ⋯
/-- The comparison map on étale cohomology induced by a morphism of schemes `f : X ⟶ Y`: an
`Ext`-class out of the constant sheaf `ℤ` on the small étale site of `Y` is pushed forward
along the exact functor `f^*` and then precomposed with the comparison `ℤ_X ≅ f^* ℤ_Y` of
constant sheaves of `AlgebraicGeometry.Scheme.upperStarConstantSheafIso`.
(blueprint: `def-weil-pbc-cohomology-pullback`) -/
noncomputable def cohomologyMap :
    Sheaf.H F n →+ Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj F) n :=
  Sheaf.H.mapFunctor _
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
      (AddCommGrpCat.of (ULift ℤ))) F n
-- ⋯
variable [IsUniversalHomeomorphism f]
-- ⋯
attribute [local instance] isEquivalence_upperStar
-- ⋯
/-- **Topological invariance of étale cohomology**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y` the comparison map `AlgebraicGeometry.Etale.cohomologyMap` on
étale cohomology is bijective in every degree.
(blueprint: `prop-weil-pbc-universal-homeomorphism-topos`) -/
@[stacks 03SI]
theorem cohomologyMap_bijective : Function.Bijective (cohomologyMap f F n) :=
  Sheaf.H.mapFunctor_bijective _ _ F n
```

### C.10 Route (i) of bridge F3: limit cones over finite subextensions, Tag 09YQ for `Sheaf.H`, and the composition rule

`Spec ks` as the limit of the `Spec K` over the finite subextensions `K` of an algebraic extension `ks / k` (`AlgebraicGeometry.FiniteIntermediateField.isLimitSpecCone`):

`WeilConjectures/AlgebraicGeometry/IntermediateFieldLimit.lean`, lines 30, 32, 34, 36, 38, 44, 83–85, 109–113, 207, 255–259:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
namespace AlgebraicGeometry
-- ⋯
variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks]
-- ⋯
namespace FiniteIntermediateField
-- ⋯
/-- The cofiltered diagram `K ↦ Spec K` over the finite subextensions `K` of `ks / k`. -/
noncomputable def specDiagram : (FiniteIntermediateField k ks)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram k ks).op ⋙ Scheme.Spec
-- ⋯
/-- The cone over `specDiagram k ks` with point `Spec ks`. -/
noncomputable def specCone : Cone (specDiagram k ks) where
  pt := Spec (.of ks)
  π := { app K := Spec.map (CommRingCat.ofHom (algebraMap K.unop.1 ks))
         naturality _ _ f := (Scheme.Spec.mapCone (ringCocone k ks).op).π.naturality f }
-- ⋯
variable [Algebra.IsAlgebraic k ks]
-- ⋯
/-- **`Spec ks` is the cofiltered limit of the `Spec K`** for the finite subextensions `K` of an
algebraic extension `ks / k`. -/
noncomputable def isLimitSpecCone : IsLimit (specCone k ks) :=
  (isLimitOfPreserves Scheme.Spec (isColimitRingCocone k ks).op).ofIsoLimit
    (Cone.ext (Iso.refl _) fun _ ↦ by simp)
```

The same cone as a cone of schemes over `Spec L` (`overDiagram`, `overCone`, `isLimitOverCone`):

`WeilConjectures/SixFunctors/ProEtale/GaloisAcyclic/FieldExtension.lean`, lines 40, 42, 44, 46, 48, 50, 60–67, 78–85, 87, 89–91:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
namespace FiniteIntermediateField
-- ⋯
variable (L Ω : Type u) [Field L] [Field Ω] [Algebra L Ω]
-- ⋯
/-- The diagram `K ↦ Spec K` of the finite subextensions `K` of `Ω / L`, as schemes over
`Spec L`. -/
@[simps]
noncomputable def overDiagram : (FiniteIntermediateField L Ω)ᵒᵖ ⥤ Over (Spec (.of L)) where
  obj K := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L K.unop.1)))
  map f := Over.homMk (specMap (leOfHom f.unop)) (specMap_comp_specMap_algebraMap L Ω _)
  map_id K := Over.OverMorphism.ext ((specDiagram L Ω).map_id K)
  map_comp f g := Over.OverMorphism.ext ((specDiagram L Ω).map_comp f g)
-- ⋯
/-- The cone with point `Spec Ω` over `overDiagram L Ω`. -/
@[simps]
noncomputable def overCone : Cone (overDiagram L Ω) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
  π :=
    { app K := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K.unop.1 Ω)))
        (specMap_algebraMap_comp_specMap_algebraMap L Ω K.unop)
      naturality _ _ f := Over.OverMorphism.ext ((specCone L Ω).π.naturality f) }
-- ⋯
variable [Algebra.IsAlgebraic L Ω]
-- ⋯
/-- `Spec Ω` is the limit of the `Spec K`, `K` running over the finite subextensions of the
algebraic extension `Ω / L`, as schemes over `Spec L`. -/
noncomputable def isLimitOverCone : IsLimit (overCone L Ω) := by
```

Inside the proof of a vanishing theorem of the same file, the cone is pulled back along a scheme `W` over `Spec L`, mapped to the slice over `G`, and fed to the vanishing form of 09YQ (lines 153–159 and 176–177 of the proof). The pulled-back cone is not exported:

`WeilConjectures/SixFunctors/ProEtale/GaloisAcyclic/FieldExtension.lean`, lines 40, 42, 44, 46, 101, 103, 105, 124, 134–142, 153–159, 176–177:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
namespace ProEtale
-- ⋯
open Scheme FiniteIntermediateField
-- ⋯
variable (Λ : Type (u + 1)) [Ring Λ] {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω]
-- ⋯
variable {G : Scheme.{u}} (h : G ⟶ Spec (.of L))
-- ⋯
theorem isZero_rightDerived_sectionsFunctor_pullback_upperStar_comparisonUpperStar_obj
    [Algebra.IsAlgebraic L Ω] (W : G.ProEt) (R : CommRingCat.{u}) [IsWContractibleRing R]
    (e : W.left ≅ Spec R) (F₀ : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero (((sectionsFunctor (ModuleCat.{u + 1} Λ)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj W)).rightDerived
          (q + 1)).obj ((ProEtale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) G).obj F₀))) := by
-- ⋯
  -- `T.left = W ×_G G_Ω` is the limit of the `W ×_L K` over `G`
  let a := W.hom ≫ h
  let D := overDiagram L Ω ⋙ Over.pullback a ⋙ Over.map W.hom
  let c₀ := (Over.map W.hom).mapCone ((Over.pullback a).mapCone (overCone L Ω))
  have hc₀ : IsLimit ((Over.forget G).mapCone c₀) :=
    isLimitOfPreserves (Over.forget W.left)
      (isLimitOfPreserves (Over.pullback a) (isLimitOverCone L Ω))
-- ⋯
  exact Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit _ F₀ D (c₀.extend iso.inv)
    hc (q + 1) fun K ↦ isZero_rightDerived_etaleSectionsFunctor_of_isWContractibleRing Λ _ _ q
```

The geometric fibre `X₀ ⊗_k k̄`, `k̄ = AlgebraicClosure k`, as the limit of the finite levels `X₀ ⊗_k K`, a diagram of schemes with affine transition maps and with quasi-compact, quasi-separated levels when `X₀` is (`AlgebraicGeometry.Scheme.Hom.isLimitFiniteLevelCone`):

`WeilConjectures/WeilSheaf/CondensedModelFiniteLevelColimit.lean`, lines 65, 67, 69, 71, 92, 230, 232, 234, 275–280, 295–299, 336–337, 341–342, 345–346, 359–363:

```lean
@[expose] public section
-- ⋯
noncomputable section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Topology
-- ⋯
namespace AlgebraicGeometry
-- ⋯
namespace Scheme.Hom
-- ⋯
variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
-- ⋯
open FiniteIntermediateField
-- ⋯
/-- The cofiltered diagram `K ↦ X₀ ⊗_k K` of the finite levels, over the finite subextensions
`K` of `k̄ / k`. -/
@[simps]
def finiteLevelDiagram : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ ⥤ Scheme.{u} where
  obj K := f.finiteLevel K.unop.1
  map g := f.finiteLevelMap (leOfHom g.unop)
-- ⋯
/-- The geometric fibre `X̄ = X₀ ⊗_k k̄`, as a cone over the finite levels. -/
@[simps pt]
def finiteLevelCone : Cone f.finiteLevelDiagram where
  pt := f.geometricFiber
  π := { app K := f.geometricFiberToFiniteLevel K.unop.1.val
-- ⋯
instance {K K' : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ} (g : K ⟶ K') :
    IsAffineHom (f.finiteLevelDiagram.map g) :=
-- ⋯
instance [CompactSpace X₀] (K : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ) :
    CompactSpace (f.finiteLevelDiagram.obj K) :=
-- ⋯
instance [QuasiSeparatedSpace X₀] (K : (FiniteIntermediateField k (AlgebraicClosure k))ᵒᵖ) :
    QuasiSeparatedSpace (f.finiteLevelDiagram.obj K) :=
-- ⋯
/-- **The geometric fibre is the limit of the finite levels**: `X₀ ⊗_k k̄ = lim_K X₀ ⊗_k K` over
the finite subextensions `K` of `k̄ / k`, since `Spec k̄ = lim_K Spec K`
(`AlgebraicGeometry.FiniteIntermediateField.isLimitSpecCone`) and base change commutes with
connected limits. -/
def isLimitFiniteLevelCone : IsLimit f.finiteLevelCone :=
```

Tag 09YQ for `Sheaf.H` of an abelian sheaf, in elementwise form along `Etale.cohomologyMap` (`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`):

`WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean`, lines 47, 49, 51, 53, 55, 110–127:

```lean
@[expose] public section
-- ⋯
universe u' u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
-- ⋯
/-- Étale cohomology continuity, elementwise form: for a cofiltered system `(Dᵢ)` of
quasi-compact quasi-separated schemes over `S` with affine transition maps and limit `X = c.pt`,
and an abelian étale sheaf `F` on `S`, `Hᵠ(X, F|_X) = colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ})` along
`AlgebraicGeometry.Etale.cohomologyMap`: every class on `X` comes from some `Dᵢ` (via
`F|_X ≅ (F|_{Dᵢ})|_X`), and a class on `Dᵢ` vanishing on `X` vanishes on some `Dⱼ`, `j ⟶ i`. -/
theorem cohomologyMap_isColimit_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    (∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x) ∧
    ∀ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
      Etale.cohomologyMap (c.π.app i).left _ q y = 0 →
        ∃ (j : I) (g : j ⟶ i), Etale.cohomologyMap (D.map g).left _ q y = 0 := by
```

Naturality in the sheaf and the composition rule for `Etale.cohomologyMap` (`AlgebraicGeometry.Etale.cohomologyPullbackFunctorial`):

`WeilConjectures/AlgebraicGeometry/EtaleCohomologyPullbackFunctorial.lean`, lines 22, 24, 26–27, 29, 31–49:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory
open AlgebraicGeometry
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
set_option backward.isDefEq.respectTransparency false in
/-- The pullback on étale cohomology is natural in the sheaf and compatible with composition of
morphisms: clauses (3) and (4) of proposition-cohomology-p-1-over-henselian--1. Independence
of resolutions and the remaining clauses are not stated here. -/
theorem cohomologyPullbackFunctorial {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (∀ {G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (φ : F ⟶ G) (x : Sheaf.H F q),
      cohomologyMap (u ≫ v) G q (Sheaf.H.map φ q x) =
        Sheaf.H.map (((u ≫ v)^*[AddCommGrpCat.{u + 1}]).map φ) q
          (cohomologyMap (u ≫ v) F q x)) ∧
    (∀ (x : Sheaf.H F q),
      cohomologyMap u ((v)^*[AddCommGrpCat.{u + 1}].obj F) q
          (cohomologyMap v F q x) =
        Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} u v).hom.app F) q
          (cohomologyMap (u ≫ v) F q x)) ∧
    (∀ (x : Sheaf.H F q),
      Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} Z).hom.app F) q
        (cohomologyMap (𝟙 Z) F q x) = x) := by
```

The factorization of a geometric point through its strict localization (`AlgebraicGeometry.Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase`):

`WeilConjectures/AlgebraicGeometry/Sites/StrictHenselizationLocal.lean`, lines 35, 37, 39, 41, 43, 427–431:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite Polynomial
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
-- ⋯
set_option backward.isDefEq.respectTransparency false in
/-- The geometric point `s` is the composite of `Spec` of the evaluation map
`𝒪^{sh}_{S,s} ⟶ Ω` with the structure morphism `S_(s) ⟶ S`. -/
lemma spec_map_strictHenselizationEval_comp_strictLocalizationToBase :
    Spec.map (strictHenselizationEval s) ≫ strictLocalizationToBase s = s := by
```

Its use over a field together with the universal homeomorphism `Spec K̄ ⟶ Spec K_(s)`, inside the proof of a cohomological-dimension bound (lines 112–127 of the proof):

`WeilConjectures/AlgebraicGeometry/Sites/FieldCohomologicalDimension.lean`, lines 36, 38, 40, 42, 45, 95–105, 112–127:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped AlgebraicGeometry.Etale
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
/-- Descent of a geometric cohomological dimension bound.

Let `X` be a scheme of finite type over a field `K` (structure morphism `a`), and let `K̄` be an
algebraic closure of `K`. If `cd_tor(K) ≤ c` and `cd_tor(X_K̄) ≤ e`, then `cd_tor(X) ≤ c + e`. -/
theorem hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] {c e : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c)
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e) :
    X.HasTorsionCohomologicalDimensionLE (c + e) := by
-- ⋯
  let s₀ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  -- the higher direct images vanish above `e`
  have hvan (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
      (hq : e < q) : IsZero ((((a)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F) := by
    let T := strictLocalizationToBase s₀ ≫ 𝟙 (Spec (.of K))
    let u := Spec.map (strictHenselizationEval s₀)
    have hu : IsUniversalHomeomorphism u := isUniversalHomeomorphism_spec_strictHenselizationEval
    have hs : s₀ = u ≫ T := by
      simp only [T, Category.comp_id]
      exact (spec_map_strictHenselizationEval_comp_strictLocalizationToBase s₀).symm
    let φ : pullback a s₀ ⟶ pullback a T :=
      (pullback.congrHom rfl hs).hom ≫ (pullbackLeftPullbackSndIso a T u).inv ≫ pullback.fst _ _
    have hP := hX.of_isUniversalHomeomorphism φ
    refine isZero_of_isZero_upperStar_of_surjective (s₀ ≫ 𝟙 _) ?_ _
      (Etale.isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H a (𝟙 _) F s₀ q (by lia)
        (hP _ (Etale.isTorsion_upperStar _ hF) q hq))
```

### C.11 Comparisons of FAG's cohomology groups, and the cospecialization map (inputs to bridges F1, F3 and F5)

`Ext` over `Λ` against `Sheaf.H` of the underlying abelian sheaf, for every sheaf of `Λ`-modules (`AlgebraicGeometry.Etale.bijective_mapExtComp_constantIntToRing`), and the special case of the unit (`unitShiftAddEquivH`):

`WeilConjectures/SixFunctors/Etale/ConstantCohomologyExt.lean`, lines 25, 27, 29, 31, 33, 65–71, 87–93:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite Abelian MonoidalCategory
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
-- ⋯
/-- **`Ext` over `Λ` is abelian cohomology.** On a quasi-compact quasi-separated scheme, for
every étale sheaf `Y` of `Λ`-modules, `e ↦ u ∘ e`, `Ext^n(Λ_X, Y) ⟶ Hⁿ(X_ét, Y)`, is bijective,
where `u : ℤ_X ⟶ Λ_X` is the class of `1`. -/
theorem bijective_mapExtComp_constantIntToRing [CompactSpace X] [QuasiSeparatedSpace X]
    (Y : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Function.Bijective ((sheafForget₂ Λ X).mapExtComp
      (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ) Y n) := by
-- ⋯
/-- **Classes in `D(X_ét, Λ)` are abelian cohomology classes.** On a quasi-compact
quasi-separated scheme, `Hom(Λ_X, Λ_X[n])` in `D(X_ét, Λ)` is the abelian cohomology group
`Hⁿ(X_ét, Λ)` of the underlying abelian sheaf of `Λ_X`. -/
noncomputable def unitShiftAddEquivH [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) :
    (𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) ≃+
      Sheaf.H ((sheafForget₂ Λ X).obj
        (Sheaf.constantRing X.smallEtaleTopology Λ)) n :=
```

Derived global sections of a sheaf of `Λ`-modules against those of the underlying abelian sheaf (`AlgebraicGeometry.Etale.forgetRightDerivedSectionsIso`):

`WeilConjectures/SixFunctors/Etale/ForgetModuleCohomology.lean`, lines 29, 31, 33, 35, 37, 98–107:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry.Etale
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
-- ⋯
/-- **Cohomology of a sheaf of modules is that of the underlying abelian sheaf**, for any ring
`Λ`: on a quasi-compact quasi-separated scheme, the derived global sections `Rᵠ Γ(X_ét, G)`,
computed in sheaves of `Λ`-modules, are, as an abelian group, those of the underlying abelian
sheaf. -/
noncomputable def forgetRightDerivedSectionsIso [CompactSpace X] [QuasiSeparatedSpace X]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (((sectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived q).obj G) ≅
      ((sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerived q).obj
        ((sheafForget₂ Λ X).obj G) :=
```

The cospecialization map `F_s ⟶ F_{t ≫ g}` for a geometric point `t` of the strict localization `g : S_(s) ⟶ S` (`AlgebraicGeometry.Scheme.cospecializationMap`):

`WeilConjectures/AlgebraicGeometry/Sites/Cospecialization.lean`, lines 30, 32, 34, 108, 110, 180, 182, 207, 209–217:

```lean
@[expose] public section
-- ⋯
universe w r v u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
-- ⋯
section Cospecialization
-- ⋯
variable {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s)
-- ⋯
variable (A : Type*) [Category A] [HasColimitsOfSize.{u, u} A]
-- ⋯
/-- The **cospecialization map** `F_s ⟶ F_t` of a sheaf `F` on the small étale site of `S`,
from the stalk at a geometric point `s` to the stalk at a geometric point
`t ≫ (S_(s) ⟶ S)` coming from a geometric point `t` of the strict localization `S_(s)`: the
germ of a section at a pointed étale neighbourhood `(V, v)` of `s` is sent to its germ at the
point `t` followed by the leg `S_(s) ⟶ V`. For `F` a sheaf, `F_s = Γ(S_(s), F|_{S_(s)})`, and
this is the restriction to the geometric point `t`. -/
noncomputable def cospecializationMap (F : Sheaf S.smallEtaleTopology A) :
    (pointSmallEtale s).sheafFiber.obj F ⟶
      (pointSmallEtale (t ≫ strictLocalizationToBase s)).sheafFiber.obj F :=
```

Its bijectivity when restriction of sections over the strict localization to `t` is an isomorphism, for any sheaf of `Λ`-modules on any scheme (`AlgebraicGeometry.Scheme.bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap`):

`WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/CospecializationSections.lean`, lines 36, 38, 40, 42, 139, 141, 278–289:

```lean
@[expose] public section
-- ⋯
universe u' u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
open scoped AlgebraicGeometry.Etale
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {Λ : Type (u + 1)} [CommRing Λ]
-- ⋯
/-- **The cospecialization map is the restriction of sections over the strict localization.**
Let `s : Spec Ω ⟶ Y` be a geometric point with strict localization `g : Y_(s) ⟶ Y` and
`t : Spec Ω' ⟶ Y_(s)` a geometric point. For a sheaf `G` of `Λ`-modules on `Y_ét`, if
restriction of global sections `Γ(Y_(s), g^* G) ⟶ Γ(Spec Ω', t^* g^* G)` is an isomorphism,
then the cospecialization map `G_s ⟶ G_{t ≫ g}` is bijective. -/
theorem bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap {Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((strictLocalizationToBase s)^*[ModuleCat.{u + 1} Λ].obj G))) :
    Function.Bijective (cospecializationMap s t (ModuleCat.{u + 1} Λ) G).hom := by
```

FAG combines it with the specialization theorem of C.1 (line 180 of the same file) in the proof of its local-constancy form; the combination (lines 241–247) uses no field:

`WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/SmoothProperLocallyConstant.lean`, lines 49, 51, 53, 55, 57, 59, 61, 226–247:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
variable (Λ : Type (u + 1)) [CommRing Λ]
-- ⋯
theorem Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [Smooth f] [IsProper f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] (q : ℤ) :
    IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  obtain ⟨N, hN₀, hN, hNk⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Spec (.of k))
  have hNY : IsUnit (N : Γ(Y, ⊤)) := by simpa using hNk.map aY.appTop.hom
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have hF : IsConstructibleSheaf F :=
    ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩
  have := Etale.hasConstructibleDirectImages_of_isProper (Λ := Λ) aY f F hF q
  refine isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap _ fun s _ _ _ t ↦
    bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap s t _ ?_
  have := Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper Λ f N
    hN₀.ne' hN hNY F s t q
  exact @Etale.isIso_globalSectionsUpperStarMap_of_iso _ _ _ _ t _ _ (Iso.symm
    ((strictLocalizationToBase s)^*[ModuleCat.{u + 1} Λ].mapIso
      (Etale.homologyRightDerivedLowerStarSingleIsoPlus f F q))) this
```

The image of the boundary specialization map of C.7 is the module of inertia invariants, under further hypotheses (`AlgebraicGeometry.Etale.range_boundarySpecialization`); bridge F5 does not need it:

`WeilConjectures/EtaleCohomology/Purity/RealSheaves/BoundaryStalk.lean`, lines 46, 48, 50, 52, 54, 56, 58–62, 64–67, 207, 209–211, 302, 304, 306–314, 316–322:

```lean
@[expose] public section
-- ⋯
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme Scheme.FiniteEtale
-- ⋯
namespace Etale
-- ⋯
variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsIntegral C]
  [Nonempty U] {W : C.Opens} [Fact (IsAffineOpen W)] [Nonempty W]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal] {Λ : Type (u + 1)} [Ring Λ]
-- ⋯
/-- The geometric point `x̄ : Spec κ(B_Q) ⟶ Spec B_Q ⟶ C` over the boundary point. -/
noncomputable abbrev boundaryGeometricPoint :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime Q))) ⟶ C :=
  closedGeometricPoint (Localization.AtPrime Q) ≫ specAtPrime Fact.out Q
-- ⋯
section Surjective
-- ⋯
variable [QuasiCompact j] [IsDedekindDomain Γ(C, W)] (ϖ : Γ(C, W)) (hϖ : ϖ ≠ 0)
  (hWU : j.opensRange ⊓ W = C.basicOpen ϖ) (m : Ideal Γ(C, W)) [m.IsMaximal]
  [PerfectField m.ResidueField] [Q.LiesOver m]
-- ⋯
section Invariants
-- ⋯
variable {Λ : Type (u + 1)} [CommRing Λ] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
-- ⋯
omit [IsSepClosed Ω] [Nonempty W] [Fact (IsAffineOpen W)] [IsOpenImmersion j] in
/-- The inertia invariants `F_η^I` of the geometric generic stalk. -/
def inertiaInvariants :
    Submodule Λ ((pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :
      ModuleCat.{u + 1} Λ) where
  carrier := {x | ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω), galoisStalkMap F σ x = x}
  add_mem' {a b} ha hb σ hσ := by rw [map_add, ha σ hσ, hb σ hσ]
  zero_mem' σ _ := map_zero _
  smul_mem' c x hx σ hσ := by rw [map_smul, hx σ hσ]
-- ⋯
include hϖ hWU m in
/-- Blueprint `lemma-boundary-stalk--1`: the image of the specialization map is the
module of inertia invariants of the geometric generic stalk. -/
theorem range_boundarySpecialization [Finite Λ] [ConnectedSpace U]
    (hint : ∀ Y : U.FiniteEtale, PreGaloisCategory.IsConnected Y → IsIntegral Y.obj.left)
    [IsFiniteLocallyConstantSheaf F] :
    Set.range (boundarySpecialization j Q F) = inertiaInvariants j Q F := by
```

### C.12 The strict localization as a universal strictly henselian scheme, and the germ formulas of the two specialization maps (inputs to bridge F5)

For a geometric point `s : Spec Ω ⟶ S`, a strictly henselian local scheme `Spec B` over `S` with a geometric point `p₀` over `s` and over the closed point maps to `S_(s)` over `S`, carrying `p₀` to the canonical geometric point (`AlgebraicGeometry.Scheme.exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing`). Two morphisms from a local scheme to `S_(s)` that agree over `S` and after composition with a morphism hitting the closed point are equal (`AlgebraicGeometry.Scheme.hom_strictLocalization_ext`):

`WeilConjectures/AlgebraicGeometry/Sites/StrictLocalizationUniversal.lean`, lines 34, 36, 38, 110, 127, 129–136, 142, 165–173:

```lean
universe u
-- ⋯
open CategoryTheory Limits
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
-- ⋯
variable {B : Type u} [CommRing B]
-- ⋯
/-- **Uniqueness of morphisms to the strict localization.** Two morphisms from a local scheme
`Spec B` to the strict localization `S_(s)` which agree over `S` and after composition with a
morphism `p₀` hitting the closed point are equal. -/
lemma hom_strictLocalization_ext {R : CommRingCat.{u}} [IsLocalRing R]
    {ℓ₁ ℓ₂ : Spec R ⟶ strictLocalization s}
    (h : ℓ₁ ≫ strictLocalizationToBase s = ℓ₂ ≫ strictLocalizationToBase s)
    {T : Scheme.{u}} (p₀ : T ⟶ Spec R) (t : T) (ht : p₀ t = IsLocalRing.closedPoint R)
    (hp₀ : p₀ ≫ ℓ₁ = p₀ ≫ ℓ₂) : ℓ₁ = ℓ₂ := by
-- ⋯
variable [IsStrictlyHenselianLocalRing B]
-- ⋯
/-- **Existence of morphisms to the strict localization.** A strictly henselian local scheme
`Spec B` over `S` with a geometric point `p₀` over `s` and over the closed point maps to the
strict localization `S_(s)` over `S`, carrying `p₀` to the canonical geometric point. -/
theorem exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing (a : Spec (.of B) ⟶ S)
    (p₀ : Spec (.of Ω) ⟶ Spec (.of B))
    (hp₀ : p₀ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint B) (ha : p₀ ≫ a = s) :
    ∃ k : Spec (.of B) ⟶ strictLocalization s,
      k ≫ strictLocalizationToBase s = a ∧
        p₀ ≫ k = Spec.map (strictHenselizationEval s) := by
```

The localization at a prime `Q` of the integral closure of `R` in a separably closed field `Ω` algebraic over `R` is strictly henselian when `R → Ω` is injective (`Ideal.isStrictlyHenselianLocalRing_atPrime`):

`WeilConjectures/RingTheory/StrictlyHenselianNormal.lean`, lines 27, 42, 44–45, 47–48, 67, 69, 71–74:

```lean
open IsLocalRing
-- ⋯
namespace Ideal
-- ⋯
variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
-- ⋯
/-- The localization at a prime `Q` of the integral closure of `R` in a field `Ω` maps to `Ω`. -/
noncomputable def atPrimeToField : Localization.AtPrime Q →+* Ω :=
-- ⋯
section StrictlyHenselian
-- ⋯
variable [IsSepClosed Ω] [Algebra.IsAlgebraic R Ω]
-- ⋯
/-- The localization at a prime of the integral closure of a domain `R` in a separably closed
field `Ω` algebraic over `R` is strictly henselian. -/
theorem isStrictlyHenselianLocalRing_atPrime (hR : Function.Injective (algebraMap R Ω)) :
    IsStrictlyHenselianLocalRing (Localization.AtPrime Q) := by
```

The germ formula of the cospecialization map (C.11): the germ at a pointed étale neighbourhood `(V, v)` of `s` goes to the germ at `(V, t ≫ (S_(s) ⟶ V))` (`AlgebraicGeometry.Scheme.toPresheafFiber_cospecializationMap`):

`WeilConjectures/AlgebraicGeometry/Sites/Cospecialization.lean`, lines 32, 34, 108, 110, 180, 182, 207, 222–229:

```lean
universe w r v u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry.Scheme
-- ⋯
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
-- ⋯
section Cospecialization
-- ⋯
variable {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s)
-- ⋯
variable (A : Type*) [Category A] [HasColimitsOfSize.{u, u} A]
-- ⋯
/-- The cospecialization map on germs: the germ at `(V, v)` of a section is sent to its germ at
`(V, t ≫ (S_(s) ⟶ V))`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_cospecializationMap (F : Sheaf S.smallEtaleTopology A)
    (x : PointedEtaleNeighborhood s) :
    (pointSmallEtale s).toPresheafFiber x.1 x.2 F.obj ≫ cospecializationMap s t A F =
      (pointSmallEtale (t ≫ strictLocalizationToBase s)).toPresheafFiber x.1
        ((cospecializationNeighborhoodFunctor s t).obj x).2 F.obj :=
```

The specialization map of the stalks of a direct image and its germ formula: the germ at `(V, v)` goes to the germ at the specialization of `v`, the lift of `η` through the unique lift `Spec A ⟶ V` of `v` (`AlgebraicGeometry.Scheme.specializationFiber`, `AlgebraicGeometry.Etale.specializationStalk`, `AlgebraicGeometry.Etale.toPresheafFiber_specializationStalk`):

`WeilConjectures/ConstructibleSheaf/LowerStarSpecialization.lean`, lines 47, 49, 51, 53, 55, 118, 120–123, 130–136, 219, 221, 223, 225–228, 230–237, 244–252:

```lean
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme
-- ⋯
namespace Scheme
-- ⋯
section Specialization
-- ⋯
variable {X U : Scheme.{u}} (j : U ⟶ X) {A : Type u} [CommRing A]
  [IsStrictlyHenselianLocalRing A] (a : Spec (.of A) ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ι : CommRingCat.of A ⟶ CommRingCat.of Ω) (η : Spec (.of Ω) ⟶ U)
  (hη : η ≫ j = Spec.map ι ≫ a)
-- ⋯
/-- **Specialization on fibre functors.** A lift `v : Spec κ ⟶ V` of the closed geometric point
`Spec κ ⟶ Spec A ⟶ X` to an étale `X`-scheme `V` lifts uniquely to `Spec A ⟶ V`
(`AlgebraicGeometry.Scheme.henselianLift`); composing with `Spec Ω ⟶ Spec A` and pairing with
`η` gives a lift of `η` to `V ×_X U`. -/
noncomputable def specializationFiber (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    (pointSmallEtale η).fiber.obj ((MorphismProperty.Over.pullback @Etale ⊤ j).obj V) :=
-- ⋯
end Scheme
-- ⋯
namespace Etale
-- ⋯
section Specialization
-- ⋯
variable {X U : Scheme.{u}} (j : U ⟶ X) {A : Type u} [CommRing A]
  [IsStrictlyHenselianLocalRing A] (a : Spec (.of A) ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ι : CommRingCat.of A ⟶ CommRingCat.of Ω) (η : Spec (.of Ω) ⟶ U)
  (hη : η ≫ j = Spec.map ι ≫ a) {Λ : Type (u + 1)} [Ring Λ]
-- ⋯
/-- **The specialization map of the stalks of a direct image.** For `A` strictly henselian with
closed geometric point `s̄ : Spec κ ⟶ Spec A ⟶ X` and a geometric point `η : Spec Ω ⟶ U` over
`Spec Ω ⟶ Spec A ⟶ X`, the map `(j_* F)_{s̄} ⟶ F_η` sending the germ at `(V, v)` of a section
of `F` over `V ×_X U` to its germ at the specialization of `v`
(`AlgebraicGeometry.Scheme.specializationFiber`). -/
noncomputable def specializationStalk (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (closedGeometricPoint A ≫ a)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ⟶ (pointSmallEtale η).sheafFiber.obj F :=
-- ⋯
@[reassoc (attr := simp)]
lemma toPresheafFiber_specializationStalk
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    (pointSmallEtale _).toPresheafFiber V v
        ((sheafToPresheaf _ _).obj ((j)_*[ModuleCat.{u + 1} Λ].obj F)) ≫
        specializationStalk j a ι η hη F =
      (pointSmallEtale η).toPresheafFiber _ (specializationFiber j a ι η hη V v)
        ((sheafToPresheaf _ _).obj F) :=
```

`boundarySpecialization` (C.7) is `specializationStalk` for `A = B_Q`, `a = specAtPrime Q` and `ι = atPrimeToField Q`:

`WeilConjectures/EtaleCohomology/Purity/RealSheaves/BoundaryStalk.lean`, lines 48, 50, 52, 54, 56, 58–62, 64–67, 87–96:

```lean
universe u
-- ⋯
open CategoryTheory Limits Opposite
-- ⋯
namespace AlgebraicGeometry
-- ⋯
open Scheme Scheme.FiniteEtale
-- ⋯
namespace Etale
-- ⋯
variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsIntegral C]
  [Nonempty U] {W : C.Opens} [Fact (IsAffineOpen W)] [Nonempty W]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal] {Λ : Type (u + 1)} [Ring Λ]
-- ⋯
/-- The geometric point `x̄ : Spec κ(B_Q) ⟶ Spec B_Q ⟶ C` over the boundary point. -/
noncomputable abbrev boundaryGeometricPoint :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime Q))) ⟶ C :=
  closedGeometricPoint (Localization.AtPrime Q) ≫ specAtPrime Fact.out Q
-- ⋯
/-- Blueprint `lemma-boundary-stalk--1` (the comparison map): the specialization map
`(j_* F)_x̄ ⟶ F_η` from the stalk of the direct image at the geometric point over the boundary
point to the geometric generic stalk, sending the germ of a section of `F` over `V ×_C U`, for an
étale neighbourhood `V` of `x̄`, to its germ at the lift of `η` through `Spec B_Q ⟶ V`. -/
noncomputable def boundarySpecialization (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
      (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :=
  specializationStalk j (specAtPrime Fact.out Q) (CommRingCat.ofHom (Ideal.atPrimeToField Q)) _
    (pointOfAlgebra_comp_eq_specAtPrime j Fact.out Q) F
```
