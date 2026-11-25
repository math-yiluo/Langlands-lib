/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.ConePseudoCoherent
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.RingTheory.FiniteScalarSurjections
import WeilConjectures.RingTheory.FiniteConeCycleAttachmentFunctors
public import Mathlib.RingTheory.Flat.Localization

/-! # One descending step in a simultaneous finite free approximation

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace DerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem scalar_finiteFree {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : ModuleCat.{u} R)
    [Module.Free R P] [Module.Finite R P] :
    Module.Free S ((ModuleCat.extendScalars φ).obj P) ∧
      Module.Finite S ((ModuleCat.extendScalars φ).obj P) := by
  algebraize [φ]
  dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
    ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
  exact ⟨inferInstance, inferInstance⟩

private theorem cone_vanishing {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {F M : CochainComplex (ModuleCat.{u} R) ℤ} (α : F ⟶ M) (n : ℤ)
    (hiso : ∀ i : ℤ, n < i → QuasiIsoAt α i)
    (hepi : Epi (HomologicalComplex.homologyMap α n)) :
    ∀ i : ℤ, n ≤ i →
      Limits.IsZero ((CochainComplex.mappingCone α).homology i) := by
  intro i hi
  let T := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)
  have hT := mappingCone_triangle_distinguished α
  have hnext : IsIso ((homologyFunctor (ModuleCat.{u} R) (i + 1)).map (Q.map α)) := by
    have := hiso (i + 1) (by omega)
    exact (NatIso.isIso_map_iff (homologyFunctorFactors (ModuleCat.{u} R) (i + 1)) α).2
      ((quasiIsoAt_iff_isIso_homologyMap α (i + 1)).1 inferInstance)
  have hcur : Epi ((homologyFunctor (ModuleCat.{u} R) i).map (Q.map α)) := by
    have hh : Epi (HomologicalComplex.homologyMap α i) := by
      by_cases h : i = n
      · subst i; exact hepi
      · have := hiso i (by omega)
        rw [quasiIsoAt_iff_isIso_homologyMap] at this
        infer_instance
    have : Epi ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℤ) i).map α) := hh
    change Epi ((Q ⋙ homologyFunctor (ModuleCat.{u} R) i).map α)
    rw [← NatIso.naturality_2 (homologyFunctorFactors (ModuleCat.{u} R) i) α]
    infer_instance
  have hz : Limits.IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj T.obj₃) :=
    (HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂
      ((HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hcur)
      ((HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).1
        (show Mono ((homologyFunctor (ModuleCat.{u} R) (i + 1)).map T.mor₁) from
          by change Mono ((homologyFunctor (ModuleCat.{u} R) (i + 1)).map (Q.map α))
             infer_instance))
  exact hz.of_iso
    ((homologyFunctorFactors (ModuleCat.{u} R) i).app (CochainComplex.mappingCone α)).symm


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem finite_cone {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {F M : CochainComplex (ModuleCat.{u} R) ℤ} (α : F ⟶ M) (b n : ℤ)
    (hM : IsPseudoCoherent (Q.obj M))
    (hlower : F.IsStrictlyGE n) (hupper : F.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i))
    (hvan : ∀ i : ℤ, n ≤ i →
      Limits.IsZero ((CochainComplex.mappingCone α).homology i)) :
    Module.Finite R ((CochainComplex.mappingCone α).homology (n - 1)) := by
  have hF : IsMPseudoCoherent ((n - 1) + 1) (Q.obj F) := by
    refine ⟨F, n, b, hlower, hupper, hfinite, 𝟙 _, ?_, ?_⟩
    · intro i hi; rw [CategoryTheory.Functor.map_id]; infer_instance
    · rw [CategoryTheory.Functor.map_id]; infer_instance
  have hM' := (isPseudoCoherent_iff_forall_isMPseudoCoherent R M).1 hM (n - 1)
  have hD := CategoryTheory.isMPseudoCoherent_cone R (n - 1)
    (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α))
    (mappingCone_triangle_distinguished α) hF hM'
  have hf := finite_homology_of_isMPseudoCoherent (n - 1)
    (CochainComplex.mappingCone α) hD (fun i hi =>
      (hvan i (by omega)).of_iso
        ((homologyFunctorFactors (ModuleCat.{u} R) i).app
          (CochainComplex.mappingCone α)))
  have : Module.Finite R ((Q ⋙ homologyFunctor (ModuleCat.{u} R) (n - 1)).obj
      (CochainComplex.mappingCone α)) := hf
  exact Module.Finite.equiv ((homologyFunctorFactors (ModuleCat.{u} R) (n - 1)).app
    (CochainComplex.mappingCone α)).toLinearEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Adjoin one finite free term to improve a simultaneous approximation by one degree.
The transition retains the old terms in degrees at least the old cutoff.

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent, the descending
construction (blueprint: lem-sc-finite-localization-free-step).

Proof: Form the cone of alpha. At every specified localization its cohomology vanishes
in degrees at least n, by the cone exact sequence and the two approximation hypotheses.
The localized source is a bounded finite free complex. Truncate the bounded above
finite free model of the localized target to obtain (n-1)-pseudo-coherence. The cone
pseudo-coherence theorem (Tag 064R) gives (n-1)-pseudo-coherence of the localized cone;
finite top cohomology (Tag 064S) makes its degree-(n-1) cohomology finite. Exactness
of localization identifies this cohomology with the scalar extension of global cone
homology. Finitely many generators in finitely many tensor products involve only
finitely many global homology elements. Their finite free map to global homology is
epic after each localization. Lift it to cone cycles by projectivity of its finite
free source. Define G by retaining F in degrees at least n, adjoining P in n-1,
and setting all lower terms to zero. The cone coordinates define the new map
component and the negative of the new differential. The cycle equation proves the
chain-map and square-zero identities. Inclusion of the old terms defines tau and
commutes with the maps to M. The cone exact sequence gives the improved approximation.
Since n-1 <= b, the upper bound is unchanged. For an empty family choose P=0; a zero
localization contributes no generators. No unit ideal hypothesis is used.
-/
theorem exists_finite_localization_free_step (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℕ) (f : Fin r → A)
    [∀ j : Fin r, HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away (f j)))]
    (hlocal : ∀ j : Fin r, IsPseudoCoherent
      (Q.obj ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).obj M)))
    (b n : ℤ) (hn : n ≤ b + 1)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (α : F ⟶ M)
    (hupper : F.IsStrictlyLE b) (hlower : F.IsStrictlyGE n)
    (hfinite : ∀ i : ℤ, Module.Free A (F.X i) ∧ Module.Finite A (F.X i))
    (hiso : ∀ j : Fin r, ∀ i : ℤ, n < i → QuasiIsoAt
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).map α) i)
    (hepi : ∀ j : Fin r, Epi (HomologicalComplex.homologyMap
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).map α) n)) :
    ∃ (G : CochainComplex (ModuleCat.{u} A) ℤ) (β : G ⟶ M),
      G.IsStrictlyLE b ∧ G.IsStrictlyGE (n - 1) ∧
      (∀ i : ℤ, Module.Free A (G.X i) ∧ Module.Finite A (G.X i)) ∧
      (∀ j : Fin r, ∀ i : ℤ, n - 1 < i → QuasiIsoAt
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map β) i) ∧
      (∀ j : Fin r, Epi (HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map β) (n - 1))) ∧
      ∃ τ : F ⟶ G, τ ≫ β = α ∧ ∀ i : ℤ, n ≤ i → IsIso (τ.f i) := by
  let L (j : Fin r) := ModuleCat.extendScalars
    (algebraMap A (Localization.Away (f j)))
  have hadd (j : Fin r) : (L j).Additive :=
    (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  have hexact (j : Fin r) : Limits.PreservesFiniteLimits (L j) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away (f j)) (Submonoid.powers (f j))))
  let LC (j : Fin r) := (L j).mapHomologicalComplex (ComplexShape.up ℤ)
  let D := CochainComplex.mappingCone α
  have hv (j : Fin r) : ∀ i : ℤ, n ≤ i →
      Limits.IsZero ((CochainComplex.mappingCone ((LC j).map α)).homology i) :=
    cone_vanishing ((LC j).map α) n (hiso j) (hepi j)
  have hfin (j : Fin r) : Module.Finite (Localization.Away (f j))
      ((CochainComplex.mappingCone ((LC j).map α)).homology (n - 1)) := by
    have := hupper
    have := hlower
    have hff (i : ℤ) : Module.Free (Localization.Away (f j)) (((LC j).obj F).X i) ∧
        Module.Finite (Localization.Away (f j)) (((LC j).obj F).X i) := by
      have hf_i : Module.Free A (F.X i) := (hfinite i).1
      have hfin_i : Module.Finite A (F.X i) := (hfinite i).2
      exact scalar_finiteFree (algebraMap A (Localization.Away (f j))) (F.X i)
    exact finite_cone ((LC j).map α) b n (hlocal j) inferInstance inferInstance hff (hv j)
  have hDvan (j : Fin r) (i : ℤ) (hi : n ≤ i) :
      Limits.IsZero (((LC j).obj D).homology i) :=
    (hv j i hi).of_iso
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
        (CochainComplex.mappingCone.mapHomologicalComplexIso α (L j)))
  have hDfin (j : Fin r) : Module.Finite (Localization.Away (f j))
      (((LC j).obj D).homology (n - 1)) := by
    have : Module.Finite (Localization.Away (f j))
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} (Localization.Away (f j)))
          (ComplexShape.up ℤ) (n - 1)).obj
          (CochainComplex.mappingCone ((LC j).map α))) := hfin j
    exact Module.Finite.equiv
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n - 1)).mapIso
        (CochainComplex.mappingCone.mapHomologicalComplexIso α (L j))).symm.toLinearEquiv
  let e (j : Fin r) (C : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
      (((LC j).obj C).homology i) ≅ (L j).obj (C.homology i) :=
    (C.sc i).mapHomologyIso (L j)
  have hfinite' (j : Fin r) : Module.Finite (Localization.Away (f j))
      ((L j).obj (D.homology (n - 1))) := by
    have := hDfin j
    exact Module.Finite.equiv (e j D (n - 1)).toLinearEquiv
  obtain ⟨k, p, hp⟩ := ModuleCat.exists_finiteFree_scalar_surjections A r
    (fun j => Localization.Away (f j))
    (fun j => algebraMap A (Localization.Away (f j))) (D.homology (n - 1)) hfinite'
  let P := ModuleCat.of A (Fin k → A)
  let q : P ⟶ D.cycles (n - 1) := Projective.factorThru p (D.homologyπ (n - 1))
  have hq (j : Fin r) : Epi ((L j).map (q ≫ D.homologyπ (n - 1))) := by
    rw [Projective.factorThru_comp]
    exact hp j
  have hvan' (j : Fin r) (i : ℤ) (hi : n ≤ i) :
      Limits.IsZero ((L j).obj (D.homology i)) := (hDvan j i hi).of_iso (e j D i).symm
  obtain ⟨G, β, τ, hl, hu, hfree, hz, hc, ht⟩ :=
    exists_finiteFree_cone_cycle_attachment_functors A r
      (fun j => Localization.Away (f j)) L M F α b n hn hlower hupper hfinite
      hvan' P q hq
  have hnew (j : Fin r) (i : ℤ) (hi : n - 1 ≤ i) :
      Limits.IsZero ((homologyFunctor (ModuleCat.{u} (Localization.Away (f j))) i).obj
        (Q.obj (CochainComplex.mappingCone ((LC j).map β)))) := by
    have hraw : Limits.IsZero (((LC j).obj (CochainComplex.mappingCone β)).homology i) :=
      (hz j i hi).of_iso (e j (CochainComplex.mappingCone β) i)
    have hcone := hraw.of_iso
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
        (CochainComplex.mappingCone.mapHomologicalComplexIso β (L j))).symm
    exact hcone.of_iso ((homologyFunctorFactors
      (ModuleCat.{u} (Localization.Away (f j))) i).app
        (CochainComplex.mappingCone ((LC j).map β)))
  refine ⟨G, β, hu, hl, hfree, ?_, ?_, τ, hc, ht⟩
  · intro j i hi
    let T := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle ((LC j).map β))
    have hT := mappingCone_triangle_distinguished ((LC j).map β)
    have hm : Mono ((homologyFunctor (ModuleCat.{u} (Localization.Away (f j))) i).map
        (Q.map ((LC j).map β))) :=
      (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
        ((hnew j (i - 1) (by omega)).eq_of_src _ _)
    have he : Epi ((homologyFunctor (ModuleCat.{u} (Localization.Away (f j))) i).map
        (Q.map ((LC j).map β))) :=
      (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
        ((hnew j i (by omega)).eq_of_tgt _ _)
    have hq : IsIso ((homologyFunctor (ModuleCat.{u} (Localization.Away (f j))) i).map
        (Q.map ((LC j).map β))) := isIso_of_mono_of_epi _
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (NatIso.isIso_map_iff
      (homologyFunctorFactors (ModuleCat.{u} (Localization.Away (f j))) i)
      ((LC j).map β)).1 hq
  · intro j
    let T := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle ((LC j).map β))
    have he : Epi ((homologyFunctor (ModuleCat.{u} (Localization.Away (f j)))
        (n - 1)).map (Q.map ((LC j).map β))) :=
      (HomologySequence.epi_homologyMap_mor₁_iff T
        (mappingCone_triangle_distinguished ((LC j).map β)) (n - 1)).2
        ((hnew j (n - 1) le_rfl).eq_of_tgt _ _)
    have hcomp : Epi ((homologyFunctor (ModuleCat.{u} (Localization.Away (f j)))
        (n - 1)).map (Q.map ((LC j).map β)) ≫
        (homologyFunctorFactors (ModuleCat.{u} (Localization.Away (f j)))
          (n - 1)).hom.app ((LC j).obj M)) := inferInstance
    rw [homologyFunctorFactors_hom_naturality] at hcomp
    have := hcomp
    exact epi_of_epi ((homologyFunctorFactors
      (ModuleCat.{u} (Localization.Away (f j))) (n - 1)).hom.app ((LC j).obj G)) _

end DerivedCategory
