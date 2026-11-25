/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.AlgebraicGeometry.QcqsOpenClosedTree.Path.QcqsOpenClosedTree
import WeilConjectures.SixFunctors.GeneratorReduction.AffineResidueLisseTree
import WeilConjectures.SixFunctors.Supporting.AffineCommonProjectiveCharts
import all WeilConjectures.SixFunctors.Constructible.ConstructibleResidueTree
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.HypercoverExistence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.WeakContractibleEquivalences

/-! # Common finite-projective charts on each affine open

Source: Bhatt--Scholze, Lemmas 6.5.5--6.5.8 and 6.6.4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem path_qcqs {T S : Scheme.{u}} {t : QcqsOpenClosedTree T}
    (p : t.Path S) : CompactSpace S ∧ QuasiSeparatedSpace S := by
  induction p with
  | root t => cases t <;> exact ⟨inferInstance, inferInstance⟩
  | openBranch _ _ _ _ _ _ ih => exact ih
  | closedBranch _ _ _ _ _ _ ih => exact ih

/-- On every affine open, two finite-Tor integral inputs admit a common finite
open--closed tree with qcqs pro-etale leaf covers and bounded finite-projective models.
This is a statement about the two inputs separately, with no tensor or completeness
claim about an operation on them.

Source: Bhatt--Scholze, proof of Lemma 6.5.5, Lemmas 6.5.6--6.5.8 and 6.6.4;
Stacks Tag 09C3, lifting finite-projective residue models.
(blueprint: lem-sf-finite-tor-affine-projective-charts).

Proof: use the integral constructibility components of both hypotheses. Choose the
finitely many residue-cohomology partitions, pull them back to the affine open,
and refine them by successive quasi-compact open/complementary closed cuts. The
residue-lisse tree theorem supplies an actual finite tree, completeness, a bounded
residue-cohomology interval, and finite module models on every qcqs weakly etale
leaf object. Its completeness proof uses limit-preserving immersion inverse image
and the normalized quotient/completion unit comparison; it needs no ambient qcqs
or invertibility hypothesis. At a leaf choose a weakly contractible affine pro-etale
cover. Apply the existing common affine projective-chart theorem to both ordinary
restrictions there. Compose its finite clopen cover with the pro-etale cover; point
surjectivity follows from the covering property and the union of the clopens.
Translate strict bounds to termwise vanishing and use uniqueness of total derived
pullback to obtain precisely the requested representative isomorphisms. The
projective splittings are those of the common-chart theorem. Empty leaves impose
no condition, and zero complexes use rank zero. -/
theorem finiteTorAffineProjectiveCharts (X : Scheme.{u})
    (K L : IntegralOnSlice.D.{u, u} l E X none)
    (hK : finiteTorConstructibleIntegral l E X K)
    (hL : finiteTorConstructibleIntegral l E X L)
    (U : X.Opens) [IsAffine U.toScheme] :
    ∃ tree : QcqsOpenClosedTree U.toScheme,
      ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf → Nonempty S →
        ∃ (c : ℕ) (A : Fin c → S.ProEt),
          (∀ i, CompactSpace (A i).left) ∧
          (∀ i, QuasiSeparatedSpace (A i).left) ∧
          (∀ x : S, ∃ i, x ∈ Set.range (A i).hom.base) ∧
          ∀ (i : Fin c) (M : IntegralOnSlice.D.{u, u} l E X none),
            M = K ∨ M = L →
            ∃ P : CochainComplex (scalarReductionSource.{u, u} l E (A i).left) ℤ,
              (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k)) ∧
              (∀ k : ℤ, ∃ r : ℕ,
                ∃ ι : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (A i).left)),
                ∃ π : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (A i).left))) ⟶ P.X k,
                ι ≫ π = 𝟙 _) ∧
              Nonempty ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E
                ((A i).hom ≫ p.toRoot ≫ U.ι)).obj M ≅ DerivedCategory.Q.obj P) := by
  classical
  obtain ⟨tree, htree⟩ := affineResidueLisseTree l E X K L hK.1 hL.1 U
  refine ⟨tree, ?_⟩
  intro S p hp hne
  have := (path_qcqs p).1
  have := (path_qcqs p).2
  have : CompactSpace (Scheme.ProEt.mk (𝟙 S)).left := (path_qcqs p).1
  have : QuasiSeparatedSpace (Scheme.ProEt.mk (𝟙 S)).left := (path_qcqs p).2
  obtain ⟨D, f, hf, g, hD, hg⟩ :=
    (AlgebraicGeometry.exists_proetale_hypercover_single_affine
      S (Scheme.ProEt.mk (𝟙 S)) inferInstance inferInstance).2.1
        (Scheme.ProEt.mk (𝟙 S)) inferInstance
  have := hf
  have := hD
  let V : S.ProEt := Scheme.ProEt.mk f
  have : IsAffine V.left := inferInstanceAs (IsAffine (Spec D))
  have : WeaklyEtale (𝟙 V.left) := inferInstanceAs (WeaklyEtale (𝟙 (Spec D)))
  have hw : ∀ (F G : Sheaf (Scheme.ProEt.topology V.left) (Type (u + 1)))
      (a : F ⟶ G), Epi a →
        Function.Surjective (a.hom.app (Opposite.op (Scheme.ProEt.mk (𝟙 V.left)))) := by
    intro F G a ha
    exact (Scheme.proetale_weakContractible_equivalences V.left
      (Scheme.ProEt.mk (𝟙 V.left))).2.1.mp
        ((Scheme.proetale_weakContractible_equivalences V.left
          (Scheme.ProEt.mk (𝟙 V.left))).1.mp
            ((Scheme.proetale_weakContractible_equivalences V.left
              (Scheme.ProEt.mk (𝟙 V.left))).2.2 D (𝟙 V.left))) F G a
  have hg' : g = (MorphismProperty.Over.homMk V.hom (Category.comp_id _) :
      V ⟶ Scheme.ProEt.mk (𝟙 S)) := by
    apply MorphismProperty.Over.Hom.ext
    exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w g)
  rw [hg'] at hg
  obtain ⟨c, O, hcov, _, hqc, hqs, hmodel⟩ :=
    affine_common_projective_charts l E X V.left (V.hom ≫ p.toRoot ≫ U.ι) hw K L
      (htree S p hp hne V.left V.hom)
  let A : Fin c → S.ProEt := fun i ↦ Scheme.ProEt.mk ((O i).ι ≫ V.hom)
  refine ⟨c, A, hqc, hqs, ?_, ?_⟩
  · have hbig : Presieve.singleton V.hom ∈ Scheme.proetalePrecoverage S := by
      rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton] at hg
      exact hg
    have hsurj := (Scheme.singleton_mem_precoverage_iff (P := @WeaklyEtale) V.hom).1
      hbig.2
    intro x
    obtain ⟨y, rfl⟩ := hsurj.1 x
    have hy : y ∈ (⨆ i, O i : V.left.Opens) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact ⟨i, ⟨⟨y, hi⟩, rfl⟩⟩
  · intro i M hM
    simp only [A, Scheme.ProEt.mk_hom,
      Functor.id_obj, Category.assoc]
    obtain ⟨P, a, b, _, hge, hle, hs, ⟨e⟩⟩ := hmodel i M hM
    refine ⟨P, ⟨a, b, ?_⟩, hs, ⟨?_⟩⟩
    · intro k hk
      rcases hk with hk | hk
      · exact (CochainComplex.isStrictlyGE_iff P a).mp hge k hk
      · exact (CochainComplex.isStrictlyLE_iff P b).mp hle k hk
    · exact (ordinaryDerivedIso l E
        ((O i).ι ≫ V.hom ≫ p.toRoot ≫ U.ι)).symm.app M ≪≫ e

end WeilConjectures.GeneratorReduction
