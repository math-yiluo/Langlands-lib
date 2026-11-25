/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoversTop.Over
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.LargeSetSheafification
import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import Mathlib.Topology.Algebra.OpenSubgroup
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.ContinuousMap.Algebra
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import Mathlib.Algebra.Field.ULift
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport
import WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeFiniteCoproductSupplement

/-! # Spectral integral coefficient lattices

Source: Bhatt--Scholze, Section 6.8, and blueprint main-20261015.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Local lattice existence with fixed condensed coefficients. -/
private def EtaleCoefficientLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ (U : Scheme.{u}) (f : U ⟶ X), Etale f ∧ Surjective f ∧
    CompactSpace U ∧ QuasiSeparatedSpace U ∧
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U),
      LocallyFree (condensedRingObj A U) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj P)

/-- Transport lattice existence along an equality of coefficient maps. -/
private theorem etaleCoefficientLattice_congr
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a b : A ⟶ B) [IsMonHom a] [IsMonHom b] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (h : a = b) (hP : EtaleCoefficientLattice A B a X P) :
    EtaleCoefficientLattice A B b X P := by
  cases h
  exact hP

/-- Local lattice existence as a predicate of the actual subring. -/
private def EtaleLatticeOverSubring {E : Type} [NontriviallyNormedField E] (A : Subring E)
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) : Prop :=
  EtaleCoefficientLattice (Profinite.continuousMapRingObj A) (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap A.subtype continuous_subtype_val)) X P

/-- Transport the existing local lattice along the equality of valuation subrings. -/
private theorem normedLisse_etale_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    EtaleLatticeOverSubring (Padic.coefficientExtensionIntegers l E) X P := by
  have h0 : EtaleCoefficientLattice (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E) X P := continuousLisse_etale_lattice l E X P hP
  have h : EtaleLatticeOverSubring (continuousIntegers l E) X P :=
    etaleCoefficientLattice_congr (integralCoeff l E) (Profinite.continuousMapRingObj E)
      (integralScalarMap l E)
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (continuousIntegers l E).subtype continuous_subtype_val)) X P rfl h0
  exact Eq.mp (congrArg (fun A ↦ EtaleLatticeOverSubring A X P)
    (continuousIntegers_eq l E)) h

/-- Topological ring structure transported to an equal field structure. -/
private theorem normedField_topologicalRing (E : Type) (nE : NontriviallyNormedField E)
    (F : Field E) (h : nE.toField = F) :
    letI := nE
    letI : Field E := F
    IsTopologicalRing E := by
  cases h
  let := nE
  infer_instance

/-- The coefficient rings together with their inclusion. -/
private structure CoefficientDiagram where
  integral : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  rational : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  map : integral ⟶ rational

/-- Package actual coefficient rings and their map. -/
private def coefficientDiagramOfMap
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] : CoefficientDiagram.{u} :=
  ⟨CommMon.mk A, CommMon.mk B, CommMon.homMk (Mon.ofHom a)⟩

/-- Local lattice existence depending on a bundled coefficient diagram. -/
private def DiagramLocalLattice (D : CoefficientDiagram.{u}) (X : Scheme.{u}) : Prop :=
  ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj D.rational.X X),
    LocallyFree (condensedRingObj D.rational.X X) P →
    EtaleCoefficientLattice D.integral.X D.rational.X D.map.hom.hom X P

/-- Package a local-lattice proof without changing its coefficients. -/
private theorem diagramLocalLattice_pack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) P → EtaleCoefficientLattice A B a X P) :
    DiagramLocalLattice (coefficientDiagramOfMap A B a) X := h

/-- Unpack local-lattice existence with exactly the given coefficient map. -/
private theorem diagramLocalLattice_unpack
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (h : DiagramLocalLattice (coefficientDiagramOfMap A B a) X) :
    ∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) P → EtaleCoefficientLattice A B a X P := h

/-- The coefficient diagram in the given normed structure. -/
private def normedCoefficientDiagram
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : CoefficientDiagram.{u} :=
  coefficientDiagramOfMap
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))

/-- The same diagram with the original field and algebra retained explicitly. -/
private def originalCoefficientDiagram
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E) (hFieldEq : nE.toField = hField) :
    CoefficientDiagram.{u} := by
  let := nE
  let : Field E := hField
  let : Algebra ℚ_[l] E := hAlg
  let : IsTopologicalRing E := normedField_topologicalRing E nE hField hFieldEq
  exact coefficientDiagramOfMap
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val))

/-- Finite dimensionality transported to coherent normed algebra data. -/
private theorem normedFiniteDimensional_of_coherent
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [hFin : FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E)
    (nAlg : letI := nE; NormedAlgebra ℚ_[l] E)
    (hFieldEq : nE.toField = hField) (hAlgEq : HEq nAlg.toAlgebra hAlg) :
    letI := nE
    letI : Field E := nE.toField
    letI : Algebra ℚ_[l] E := nAlg.toAlgebra
    FiniteDimensional ℚ_[l] E := by
  cases hFieldEq
  cases eq_of_heq hAlgEq
  exact hFin

/-- Equality of algebraic structures gives equality of the coefficient diagrams. -/
private theorem coefficientDiagram_coherence
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (nE : NontriviallyNormedField E)
    (nAlg : letI := nE; NormedAlgebra ℚ_[l] E)
    (hFieldEq : nE.toField = hField) (hAlgEq : HEq nAlg.toAlgebra hAlg) :
    @normedCoefficientDiagram.{u} l _ E nE nAlg
      (normedFiniteDimensional_of_coherent l E
        (hField := hField) (hAlg := hAlg) nE nAlg hFieldEq hAlgEq) =
      originalCoefficientDiagram l E nE hFieldEq := by
  cases hFieldEq
  cases eq_of_heq hAlgEq
  rfl

/-- The normed local-lattice result as a property of its coefficient diagram. -/
private theorem normedDiagram_localLattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NontriviallyNormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    DiagramLocalLattice (normedCoefficientDiagram l E) X := by
  apply diagramLocalLattice_pack
    (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers l E))
    (Profinite.continuousMapRingObj E)
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) X
  intro P hP
  exact normedLisse_etale_lattice l E X P hP

/-- A lisse spectral-coefficient module admits an integral lattice on a qcqs etale cover.
Source: Bhatt--Scholze, Proposition 6.8.4(6) and Lemma 6.8.13, first paragraph;
blueprint main-20261015, lemma-lattices-after-finite-stratification, "Sheaf of lattices".
(blueprint: lem-sfb-spectral-etale-local-lattice).

Proof. Equip E with its spectral norm and its original field and algebra structures.
The spectral norm extends the p-adic norm. The norm-at-most-one subring is the recorded
valuation ring, by the integer-ring characterization in extension_integers_dvr.
Apply continuousLisse_etale_lattice to get a qcqs etale surjection and a locally free
integral module with its scalar-extension comparison. Transport the two coefficient
rings and their inclusion along the preceding equality, preserving the module action,
its free cover, and its rationalization. These are the same continuous-function rings
with their subspace topology. The existing etale-local proof chooses finitely many
pointed affine etale lattice neighbourhoods using Noetherian compactness and takes
their coproduct; its coproduct is affine, hence qcqs. Empty schemes give the empty
coproduct, and zero ranks remain zero. No global descent or stratification is asserted. -/
theorem spectralLisse_etale_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [hField : Field E]
    [hAlg : Algebra ℚ_[l] E] [hFin : FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap
          (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) L →
      ∃ (U : Scheme.{u}) (f : U ⟶ X), Etale f ∧ Surjective f ∧
        CompactSpace U ∧ QuasiSeparatedSpace U ∧
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U),
          LocallyFree (condensedRingObj A U) M ∧
          Nonempty ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj L) := by
  let nE := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : Field E := hField
  let : Algebra ℚ_[l] E := hAlg
  let nAlg : NormedAlgebra ℚ_[l] E :=
    { spectralNorm.normedAlgebra ℚ_[l] E with toAlgebra := hAlg }
  have h : DiagramLocalLattice (originalCoefficientDiagram l E nE rfl) X :=
    Eq.mp (congrArg (fun D ↦ DiagramLocalLattice D X)
      (coefficientDiagram_coherence l E nE nAlg rfl (HEq.refl _)))
      (normedDiagram_localLattice l E X)
  intro A B a
  exact diagramLocalLattice_unpack A B a X h

end AlgebraicGeometry.ProEtale.CondensedRing
