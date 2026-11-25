/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Projective

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

private theorem pseudoCoherent_mono
    {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (m n : ℤ) (hmn : m ≤ n) (C : DerivedCategory (ModuleCat.{v₁} R))
    (hC : IsMPseudoCoherent m C) : IsMPseudoCoherent n C := by
  obtain ⟨E, a, b, ha, hb, hfree, f, hiso, hepi⟩ := hC
  refine ⟨E, a, b, ha, hb, hfree, f, ?_, ?_⟩
  · intro i hi
    exact hiso i (by omega)
  · by_cases h : n = m
    · subst n
      exact hepi
    · have := hiso n (by omega)
      infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem finite_top_of_local
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁}
      (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (m n : ℤ) (hmn : m ≤ n)
    (hvan : ∀ j : ℤ, n < j → IsZero
      ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj M)))
    (hlocal : ∀ i : Fin r, IsMPseudoCoherent m (Q.obj ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
      (ComplexShape.up ℤ)).obj M))) : Module.Finite A (M.homology n) := by
  classical
  apply Module.Finite.of_localizationSpan (Set.range f) hf
  rintro ⟨g, i, rfl⟩
  let F := ModuleCat.extendScalars.{u₁, u₁, max u₁ v₁}
    (algebraMap A (Localization.Away (f i)))
  have : Module.Flat A (Localization.Away (f i)) :=
    IsLocalization.flat _ (Submonoid.powers (f i))
  let S := (ModuleCat.restrictScalars (algebraMap A (Localization.Away (f i)))).obj
    (ModuleCat.of (Localization.Away (f i)) (Localization.Away (f i)))
  let e : S ≃ₗ[A] Localization.Away (f i) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change algebraMap A (Localization.Away (f i)) a *
          (show Localization.Away (f i) from x) =
          a • (show Localization.Away (f i) from x)
        exact (Algebra.smul_def a (show Localization.Away (f i) from x)).symm }
  have : Module.Flat A S := Module.Flat.of_linearEquiv e
  have : F.PreservesMonomorphisms := ⟨fun {X Y} g hg ↦ by
    rw [ModuleCat.mono_iff_injective] at hg ⊢
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := S) g.hom hg⟩
  have : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  let K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  have hKvan : ∀ j : ℤ, n < j → IsZero
      ((homologyFunctor (ModuleCat.{max u₁ v₁} (Localization.Away (f i))) j).obj
        (Q.obj K)) := by
    intro j hj
    have hz : IsZero (M.homology j) :=
      (hvan j hj).of_iso ((homologyFunctorFactors _ j).symm.app M)
    have hz' : IsZero (K.homology j) :=
      (F.map_isZero hz).of_iso ((M.sc j).mapHomologyIso F)
    exact hz'.of_iso ((homologyFunctorFactors _ j).app K)
  have hK := pseudoCoherent_mono m n hmn (Q.obj K) (hlocal i)
  have : Module.Finite (Localization.Away (f i))
      ((homologyFunctor (ModuleCat.{max u₁ v₁} (Localization.Away (f i))) n).obj
        (Q.obj K)) := finite_homology_of_isMPseudoCoherent n K hK hKvan
  have : Module.Finite (Localization.Away (f i)) (K.homology n) :=
    by
      let e : ((homologyFunctor _ n).obj (Q.obj K)) ≅ K.homology n :=
        (homologyFunctorFactors _ n).app K
      exact Module.Finite.equiv e.toLinearEquiv
  have : Module.Finite (Localization.Away (f i)) (F.obj (M.homology n)) :=
    by
      let e : K.homology n ≅ F.obj (M.homology n) := (M.sc n).mapHomologyIso F
      exact Module.Finite.equiv e.toLinearEquiv
  let eT := TensorProduct.congr e (LinearEquiv.refl A (M.homology n))
  let eS : F.obj (M.homology n) ≃ₗ[Localization.Away (f i)]
      (TensorProduct A (Localization.Away (f i)) (M.homology n)) :=
    { eT.toAddEquiv with
      map_smul' := by
        intro a x
        change eT (a • x) = a • eT x
        induction x using TensorProduct.inductionOn with
        | tmul s y => rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  have : Module.Finite (Localization.Away (f i))
      (TensorProduct A (Localization.Away (f i)) (M.homology n)) := Module.Finite.equiv eS
  exact Module.Finite.equiv
    (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) (M.homology n)).symm

private theorem exists_top_approximation
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ) (n : ℤ)
    [Module.Finite A (M.homology n)] :
    ∃ (E : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ),
      E.IsStrictlyGE n ∧ E.IsStrictlyLE n ∧
      (∀ j : ℤ, Module.Free A (E.X j) ∧ Module.Finite A (E.X j)) ∧
      ∃ a : E ⟶ M, Epi ((homologyFunctor _ n).map (Q.map a)) := by
  classical
  obtain ⟨k, p, hp⟩ := Module.Finite.exists_fin' A (M.homology n)
  let P : ModuleCat.{max u₁ v₁} A := ModuleCat.of A (ULift.{v₁} (Fin k → A))
  let e : P ≃ₗ[A] (Fin k → A) := ULift.moduleEquiv
  let q : P ⟶ M.homology n := ModuleCat.ofHom (p.comp e.toLinearMap)
  have : Module.Free A P := Module.Free.of_equiv e.symm
  have : Module.Finite A P := Module.Finite.equiv e.symm
  have : Epi q := (ModuleCat.epi_iff_surjective q).2 (hp.comp e.surjective)
  let t : P ⟶ M.cycles n := Projective.factorThru q (M.homologyπ n)
  have ht : t ≫ M.homologyπ n = q := Projective.factorThru_comp _ _
  let E : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ :=
    (HomologicalComplex.single (ModuleCat.{max u₁ v₁} A) (.up ℤ) n).obj P
  let a : E ⟶ M := HomologicalComplex.mkHomFromSingle (t ≫ M.iCycles n) (by
    intro j hj
    simp only [Category.assoc]
    exact (M.iCycles_d n j).symm ▸ comp_zero)
  have hGE : E.IsStrictlyGE n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact HomologicalComplex.isZero_single_obj_X _ n P j (by omega)
  have hLE : E.IsStrictlyLE n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact HomologicalComplex.isZero_single_obj_X _ n P j (by omega)
  refine ⟨E, hGE, hLE, ?_, a, ?_⟩
  · intro j
    by_cases hj : j = n
    · subst j
      let e' := (HomologicalComplex.singleObjXSelf (.up ℤ) n P).symm.toLinearEquiv
      exact ⟨Module.Free.of_equiv e', Module.Finite.equiv e'⟩
    · have : Subsingleton (E.X j) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ n P j hj)
      exact ⟨inferInstance, inferInstance⟩
  · let s := (HomologicalComplex.singleObjXSelf (.up ℤ) n P).inv
    let l := E.liftCycles s (n + 1) (by simp) (by simp [E])
    have hl : l ≫ HomologicalComplex.cyclesMap a n = t := by
      apply (cancel_mono (M.iCycles n)).1
      dsimp only [l]
      simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
        HomologicalComplex.liftCycles_i_assoc]
      dsimp [a, s]
      rw [HomologicalComplex.mkHomFromSingle_f]
      simp only [Iso.inv_hom_id_assoc]
    have hq : (l ≫ E.homologyπ n) ≫ HomologicalComplex.homologyMap a n = q := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hl, ht]
    have : Epi (HomologicalComplex.homologyMap a n) := epi_of_epi_fac hq
    have hn := homologyFunctorFactors_hom_naturality a n
    have : Epi ((homologyFunctor _ n).map (Q.map a) ≫
        (homologyFunctorFactors _ n).hom.app M) := by
      rw [hn]
      infer_instance
    exact (epi_comp_iff_of_isIso _ ((homologyFunctorFactors _ n).hom.app M)).1 this

/-- The algebraic construction of the cone step, before the local pseudo-coherence
conclusion.  This is the finite-free approximation and cone argument from Tag 066D.
(blueprint: lem-pc-m-pseudo-coherent-localization-cone-construction). -/
theorem localization_cone_construction
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁}
      (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (m n : ℤ) (hmn : m ≤ n)
    (hvan : ∀ j : ℤ, n < j → IsZero
      ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj M)))
    (hlocal : ∀ i : Fin r, IsMPseudoCoherent m (Q.obj ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
      (ComplexShape.up ℤ)).obj M))) :
    ∃ (E N : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
      (a : Q.obj E ⟶ Q.obj M) (b : Q.obj M ⟶ Q.obj N)
      (c : Q.obj N ⟶ (Q.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang (DerivedCategory (ModuleCat.{max u₁ v₁} A)) ∧
      IsMPseudoCoherent m (Q.obj E) ∧
      (∀ j : ℤ, n - 1 < j → IsZero
        ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj N))) := by
  have : Module.Finite A (M.homology n) := finite_top_of_local M r f hf m n hmn hvan hlocal
  obtain ⟨E, hGE, hLE, hfree, a, ha⟩ := exists_top_approximation M n
  let N := CochainComplex.mappingCone a
  let T := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle a)
  have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{max u₁ v₁} A)) :=
    mappingCone_triangle_distinguished a
  refine ⟨E, N, T.mor₁, T.mor₂, T.mor₃, hT, ?_, ?_⟩
  · refine ⟨E, n, n, hGE, hLE, hfree, 𝟙 _, ?_, ?_⟩
    · intro j hj
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    · rw [CategoryTheory.Functor.map_id]
      infer_instance
  · intro j hj
    have : E.IsStrictlyLE n := hLE
    have hE : IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) (j + 1)).obj
        (Q.obj E)) := (Q.obj E).isZero_of_isLE n (j + 1) (by omega)
    apply (HomologySequence.exact₃ T hT j (j + 1)).isZero_X₂
    · by_cases h : j = n
      · subst j
        exact (HomologySequence.epi_homologyMap_mor₁_iff T hT n).1 ha
      · exact (hvan j (by omega)).eq_zero_of_src _
    · exact hE.eq_zero_of_tgt _

end DerivedCategory
