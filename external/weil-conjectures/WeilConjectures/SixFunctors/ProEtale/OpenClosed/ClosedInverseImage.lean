/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimits

/-!
# A presheaf formula for the closed inverse image

Let `i : Z = Spec (A ⧸ I) ⟶ X = Spec A` be a closed immersion with quasi-compact open complement.
On the affine ind-étale basis `B_Z` of `Z_proét`, formed by the objects
`V = Spec C̄ ≅ v(V) ×_X Z` with `C̄` ind-étale over `A ⧸ I` and `v(V) = Spec H_A(C̄)`
(`Algebra.ClosedLift`), the inverse image `i^* F` of a pro-étale sheaf of modules `F` is the
sheafification of the presheaf `P_F(V) = F(v(V))`: the map `P_F ⟶ i^* F`, given by the unit of
`i^* ⊣ i_*`, is locally surjective and locally injective on the basis
(`AlgebraicGeometry.ProEtale.closedInverseImage_formula`, blueprint
`proposition-extension-zero-restriction-closed-subscheme`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {A : CommRingCat.{u}} (I : Ideal A)

/-- The henselian lift `v(V) = Spec H_A(C̄)` of `V = Spec C̄`, for an `A ⧸ I`-algebra `C̄`
(blueprint `proposition-extension-zero-restriction-closed-subscheme`). -/
noncomputable abbrev closedLiftSpec' (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] :
    (Spec A).ProEt :=
  @closedLiftSpec A C _ (Algebra.compHom C (algebraMap A (A ⧸ I)))

variable {I}

/-- The lift `v(φ) : v(V') ⟶ v(V)` of the morphism `V' = Spec C̄' ⟶ V = Spec C̄` given by an
`A ⧸ I`-algebra map `φ : C̄ ⟶ C̄'` (blueprint
`proposition-extension-zero-restriction-closed-subscheme`). -/
noncomputable def closedLiftSpecMap {C C' : Type u} [CommRing C] [Algebra (A ⧸ I) C] [CommRing C']
    [Algebra (A ⧸ I) C'] (φ : C →ₐ[A ⧸ I] C') : closedLiftSpec' I C' ⟶ closedLiftSpec' I C :=
  let : Algebra A C := Algebra.compHom C (algebraMap A (A ⧸ I))
  let : Algebra A C' := Algebra.compHom C' (algebraMap A (A ⧸ I))
  have : IsScalarTower A (A ⧸ I) C := .of_algebraMap_eq' rfl
  have : IsScalarTower A (A ⧸ I) C' := .of_algebraMap_eq' rfl
  MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.map (φ.restrictScalars A) :
      Algebra.ClosedLift A C →+* Algebra.ClosedLift A C'))) (by
      change _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact (Algebra.ClosedLift.map (φ.restrictScalars A)).commutes a)

/-- Under the identifications `v(V) ×_X Z ≅ Spec C̄`, the base change of `v(φ)` is `Spec φ`. -/
lemma closedLiftBasisIso_hom_comp_map {C C' : Type u} [CommRing C] [Algebra (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C] [CommRing C'] [Algebra (A ⧸ I) C'] [Algebra.IndEtale (A ⧸ I) C']
    (φ : C →ₐ[A ⧸ I] C') :
    (closedLiftBasisIso I C').hom ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closedSpecι I)).map
          (closedLiftSpecMap φ)).left =
      Spec.map (CommRingCat.ofHom (φ : C →+* C')) ≫ (closedLiftBasisIso I C).hom := by
  let : Algebra A C := Algebra.compHom C (algebraMap A (A ⧸ I))
  let : Algebra A C' := Algebra.compHom C' (algebraMap A (A ⧸ I))
  have : IsScalarTower A (A ⧸ I) C := .of_algebraMap_eq' rfl
  have : IsScalarTower A (A ⧸ I) C' := .of_algebraMap_eq' rfl
  apply pullback.hom_ext
  · simp only [Category.assoc, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    change (closedLiftSpecPullbackIso I C').hom ≫ pullback.fst _ _ ≫ Spec.map _ =
      Spec.map _ ≫ (closedLiftSpecPullbackIso I C).hom ≫ pullback.fst _ _
    rw [reassoc_of% closedLiftSpecPullbackIso_hom_fst, closedLiftSpecPullbackIso_hom_fst,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact DFunLike.congr_fun
      (Algebra.ClosedLift.toAlgHom_map (φ.restrictScalars A)) x
  · simp only [Category.assoc, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
    have h₁ := closedLiftBasisIso_hom_comp I C'
    have h₂ := closedLiftBasisIso_hom_comp I C
    change (closedLiftBasisIso I C').hom ≫ (closedLiftBasisObj I C').hom =
      Spec.map _ ≫ (closedLiftBasisIso I C).hom ≫ (closedLiftBasisObj I C).hom
    rw [h₁, h₂, ← Spec.map_comp]
    congr 1
    ext r
    exact (φ.commutes r).symm

variable {R : Type (u + 1)} [Ring R] {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j]
  [QuasiCompact j]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`proposition-extension-zero-restriction-closed-subscheme`): let `i : Z = Spec (A ⧸ I) ⟶ X = Spec A`
be a closed immersion with quasi-compact open complement `j`, and `F` a pro-étale sheaf of modules
on `X`. On the affine ind-étale basis of `Z_proét`, `i^* F` is the sheafification of the presheaf
`P_F(V) = F(v(V))`, `v(V) = Spec H_A(C̄)` for `V = Spec C̄ ≅ v(V) ×_X Z`: the map
`P_F(V) ⟶ (i^* F)(V)` given by the unit of `i^* ⊣ i_*` is locally surjective and locally
injective. Explicitly, every basis object `V = Spec C̄` has a covering `Spec φ : V' ⟶ V` by a basis
object `V' = Spec C̄'` (with `C̄'` w-contractible) such that every section of `i^* F` over `V`
restricts to a section coming from `P_F(V')`, and every section of `P_F(V)` mapping to zero in
`(i^* F)(V)` restricts to zero in `P_F(V')`.

On w-contractible `V'` the map `P_F(V') ⟶ (i^* F)(V')` is even bijective
(`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`). -/
theorem closedInverseImage_formula
    (hij : IsCompl (Set.range (closedSpecι I).base) (Set.range j.base))
    (F : Sheaf (ProEt.topology (Spec A)) (ModuleCat.{u + 1} R))
    (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] [Algebra.IndEtale (A ⧸ I) C] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra (A ⧸ I) S) (_ : Algebra.IndEtale (A ⧸ I) S)
      (φ : C →ₐ[A ⧸ I] S),
      Sieve.generate (Presieve.singleton
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closedSpecι I)).map
          (closedLiftSpecMap φ))) ∈ ProEt.topology _ (closedLiftBasisObj I C) ∧
      (∀ x : ((closedSpecι I)^*[ModuleCat.{u + 1} R].obj F).obj.obj
          (op (closedLiftBasisObj I C)), ∃ t : F.obj.obj (op (closedLiftSpec' I S)),
        ((upperStarLowerStarAdjunction _ (closedSpecι I)).unit.app F).hom.app _ t =
          ((closedSpecι I)^*[ModuleCat.{u + 1} R].obj F).obj.map
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closedSpecι I)).map
              (closedLiftSpecMap φ)).op x) ∧
      ∀ s : F.obj.obj (op (closedLiftSpec' I C)),
        ((upperStarLowerStarAdjunction _ (closedSpecι I)).unit.app F).hom.app _ s = 0 →
          F.obj.map (closedLiftSpecMap φ).op s = 0 := by
  obtain ⟨S, _, _, hS₁, hS₂, hS₃⟩ := exists_isWContractibleRing C
  let : Algebra (A ⧸ I) S := Algebra.compHom S (algebraMap (A ⧸ I) C)
  have : IsScalarTower (A ⧸ I) C S := .of_algebraMap_eq' rfl
  have : Algebra.IndEtale (A ⧸ I) S := Algebra.IndEtale.trans (A ⧸ I) C S
  let : Algebra A S := Algebra.compHom S (algebraMap A (A ⧸ I))
  have : IsScalarTower A (A ⧸ I) S := .of_algebraMap_eq' rfl
  let φ : C →ₐ[A ⧸ I] S := IsScalarTower.toAlgHom (A ⧸ I) C S
  have hbij := bijective_unit_app_closedLiftSpec (C := S) j
    (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction S T) hij F
  set f := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (closedSpecι I)).map
    (closedLiftSpecMap φ)
  have hf : f.left = (closedLiftBasisIso I S).inv ≫
      Spec.map (CommRingCat.ofHom (φ : C →+* S)) ≫ (closedLiftBasisIso I C).hom := by
    rw [Iso.eq_inv_comp]
    exact closedLiftBasisIso_hom_comp_map φ
  refine ⟨S, inferInstance, inferInstance, inferInstance, φ, ?_, fun x ↦ ?_, fun s hs ↦ ?_⟩
  · have : Surjective (Spec.map (CommRingCat.ofHom (φ : C →+* S))) :=
      ((flat_and_surjective_SpecMap_iff _).2
        (RingHom.faithfullyFlat_algebraMap_iff.2 hS₂)).2
    have hsurj : Surjective ((Scheme.ProEt.forget _ ⋙ CategoryTheory.Over.forget _).map f) := by
      change Surjective f.left
      rw [hf]
      infer_instance
    have hqc : QuasiCompact ((Scheme.ProEt.forget _ ⋙ CategoryTheory.Over.forget _).map f) := by
      change QuasiCompact f.left
      rw [hf]
      infer_instance
    refine Scheme.ProEt.mem_topology_iff.2 ⟨Presieve.singleton f, ?_, Sieve.le_generate _⟩
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
    exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
      (MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) f.left
        (closedLiftBasisObj I C).hom (closedLiftBasisObj I C).prop
        (by have := MorphismProperty.Over.w f; erw [this]; exact (closedLiftBasisObj I S).prop))
  · exact hbij.2 _
  · refine hbij.1 ?_
    rw [map_zero]
    have := NatTrans.naturality_apply
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (closedSpecι I)).unit.app F).hom
      (closedLiftSpecMap φ).op s
    refine this.trans ?_
    rw [hs, map_zero]

end ProEtale

end AlgebraicGeometry
