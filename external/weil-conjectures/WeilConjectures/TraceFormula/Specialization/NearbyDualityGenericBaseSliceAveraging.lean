/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GaloisLayerStabilizationAssembly
public import WeilConjectures.TraceFormula.Specialization.GenericSliceModelAut
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseExtension
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsProof

/-!

# The slice exchange as an averaging summand

The pullback exchange `α : p^* Ψ_M ⟶ Ψ_{M''} c^*` of the projection from the generic slice model is,
at a finite level, the inclusion of the summand cut out by the averaging idempotent of a finite
group of Galois automorphisms of the slice model
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`). This is
the generic-slicing identification `g_s^* Ψ_M ≃ (Ψ_{M''} c^*)^P` of SGA 4½, [Th. finitude], §3
(Lemme 3.4 and 3.7), with the pro-`p` averaging.

It is deduced from the same statement for the base change `M_b` of `M` along the slice
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`): the generic slice
model `M''` and `M_b` have the same total space and geometric generic fibre, and the projection
`M'' ⟶ M` is the composite of the morphism `κ : M'' ⟶ M_b` with identity components
(`NearbyCyclesModel.genericSliceToBaseChange`, whose exchange is invertible and intertwines the
actions of the generic automorphisms) and of the projection `M_b ⟶ M`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-- If `k ≫ g' = L₀ f ≫ k` for an epimorphism `k` and `f = 𝟙`, then `g' = 𝟙`. -/
lemma eq_id_of_comp_eq_map_comp {E : Type*} [Category E] {L₀ : E ⥤ E} {W Z' : E}
    (k : L₀.obj W ⟶ Z') [Epi k] (f : W ⟶ W) (g' : Z' ⟶ Z') (hf : f = 𝟙 W)
    (hk : k ≫ g' = L₀.map f ≫ k) : g' = 𝟙 Z' := by
  subst hf
  rw [L₀.map_id, Category.id_comp] at hk
  exact (cancel_epi k).1 (hk.trans (Category.comp_id k).symm)

/-- **Transport of an averaging splitting along a factorization**, for abstract categories: let
`a : P₁ ⟶ Z` be identified with `L₀ β` (`β : P₀ ⟶ W`, `L₀ ≅ 𝟭`) through isomorphisms `c₁`, `k`,
`e`. If `β` is split by `rβ` with `n • (rβ ≫ β) = ∑ f i`, and the endomorphisms `f i` correspond
under `k` and `e` to endomorphisms `g i` of `Z`, then `a` is split with `n` times its idempotent
`∑ g i`. -/
lemma exists_retraction_of_averaging_conj {E : Type*} [Category E] [Preadditive E] {L₀ : E ⥤ E}
    (I : L₀ ≅ 𝟭 E) {P₀ P₁ W Z Z' : E} (a : P₁ ⟶ Z) (β : P₀ ⟶ W) (rβ : W ⟶ P₀)
    (hβ : β ≫ rβ = 𝟙 _) {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → (W ⟶ W))
    (havg : n • (rβ ≫ β) = ∑ i ∈ s, f i) (c₁ : P₁ ⟶ L₀.obj P₀) [IsIso c₁]
    (k : L₀.obj W ⟶ Z') [IsIso k] (e : Z ⟶ Z') [IsIso e] (hx : a ≫ e = c₁ ≫ L₀.map β ≫ k)
    (g : ι → (Z ⟶ Z)) (g' : ι → (Z' ⟶ Z')) (hk : ∀ i, k ≫ g' i = L₀.map (f i) ≫ k)
    (he : ∀ i, g i ≫ e = e ≫ g' i) :
    ∃ r, a ≫ r = 𝟙 _ ∧ n • (r ≫ a) = ∑ i ∈ s, g i := by
  have ha : a = c₁ ≫ L₀.map β ≫ k ≫ inv e := by
    rw [← reassoc_of% hx, IsIso.hom_inv_id, Category.comp_id]
  have hL : ∀ {U V : E} (h : U ⟶ V), L₀.map h = I.hom.app U ≫ h ≫ I.inv.app V := by
    intro U V h
    rw [← Category.comp_id (L₀.map h), ← I.hom_inv_id_app V, ← Category.assoc, I.hom.naturality h,
      Functor.id_map, Category.assoc]
  refine ⟨e ≫ inv k ≫ L₀.map rβ ≫ inv c₁, ?_, ?_⟩
  · rw [ha]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]
    rw [← L₀.map_comp_assoc, hβ, L₀.map_id, Category.id_comp, IsIso.hom_inv_id]
  · have hr : (e ≫ inv k ≫ L₀.map rβ ≫ inv c₁) ≫ a =
        (e ≫ inv k ≫ I.hom.app W) ≫ (rβ ≫ β) ≫ (I.inv.app W ≫ k ≫ inv e) := by
      rw [ha]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← L₀.map_comp_assoc, hL]
      simp only [Category.assoc]
    rw [hr, ← Preadditive.comp_nsmul, ← Preadditive.nsmul_comp, havg, Preadditive.sum_comp,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : (e ≫ inv k ≫ I.hom.app W) ≫ f i ≫ I.inv.app W ≫ k ≫ inv e =
        e ≫ inv k ≫ L₀.map (f i) ≫ k ≫ inv e := by
      rw [hL]
      simp only [Category.assoc]
    rw [hi, ← reassoc_of% (hk i), IsIso.inv_hom_id_assoc, ← reassoc_of% (he i),
      IsIso.hom_inv_id, Category.comp_id]

/-- `NearbyCyclesModel.exists_retraction_of_averaging_conj` in the shape of the composition law
`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq` for the factorization of the projection
`χ : M'' ⟶ M` through `κ : M'' ⟶ M_b` and `ψ : M_b ⟶ M` (`hx`): if the exchange `αψ` of `ψ` is
split with `n_V • (r ≫ αψ) = s_V` and `∑ f i = m • s_V` (`n = m n_V`, the counting of cosets of
nested subgroups), the exchange `ακ` of `κ` is invertible and
intertwines `f i` with `g' i`, then the exchange `αχ` of `χ` is split with `n` times its
idempotent `∑ g i`, for natural endomorphisms `g`, `g'` of `Ψ_{M''}`. -/
lemma exists_retraction_of_averaging_comp {DX DM DT D₂ : Type*} [Category DX] [Category DM]
    [Category DT] [Preadditive DT] [Category D₂] {ΨM : DX ⥤ DM} {ΨB : DX ⥤ DT} {ΨG : D₂ ⥤ DT}
    {Lp Lg : DM ⥤ DT} {L₀ : DT ⥤ DT} {L₀X : DX ⥤ DX} {Lc : DX ⥤ D₂}
    (αχ : ΨM ⋙ Lp ⟶ Lc ⋙ ΨG) (αψ : ΨM ⋙ Lg ⟶ L₀X ⋙ ΨB) (ακ : ΨB ⋙ L₀ ⟶ Lc ⋙ ΨG)
    (cp : Lp ≅ Lg ⋙ L₀) (cc : Lc ≅ L₀X ⋙ Lc) (I : L₀ ≅ 𝟭 DT) (A : DX)
    (hx : αχ.app A ≫ ΨG.map (cc.hom.app A) =
      cp.hom.app (ΨM.obj A) ≫ L₀.map (αψ.app A) ≫ ακ.app (L₀X.obj A))
    (hiso : IsIso (ακ.app (L₀X.obj A))) (rψ : (L₀X ⋙ ΨB).obj A ⟶ (ΨM ⋙ Lg).obj A)
    (hrψ : αψ.app A ≫ rψ = 𝟙 _) {ι : Type*} (s : Finset ι) (n : ℕ)
    (f : ι → (ΨB.obj (L₀X.obj A) ⟶ ΨB.obj (L₀X.obj A)))
    (m nV : ℕ) (hn : n = m * nV) (sV : ΨB.obj (L₀X.obj A) ⟶ ΨB.obj (L₀X.obj A))
    (hs : ∑ i ∈ s, f i = m • sV) (havgV : nV • (rψ ≫ αψ.app A) = sV)
    (g : ι → (ΨG.obj (Lc.obj A) ⟶ ΨG.obj (Lc.obj A)))
    (g' : ι → (ΨG.obj (Lc.obj (L₀X.obj A)) ⟶ ΨG.obj (Lc.obj (L₀X.obj A))))
    (hk : ∀ i, ακ.app (L₀X.obj A) ≫ g' i = L₀.map (f i) ≫ ακ.app (L₀X.obj A))
    (he : ∀ i, g i ≫ ΨG.map (cc.hom.app A) = ΨG.map (cc.hom.app A) ≫ g' i) :
    ∃ r, αχ.app A ≫ r = 𝟙 _ ∧ n • (r ≫ αχ.app A) = ∑ i ∈ s, g i :=
  haveI := hiso
  exists_retraction_of_averaging_conj I (αχ.app A) (αψ.app A) rψ hrψ s n f
    (by rw [hn, mul_smul, havgV, hs])
    (cp.hom.app (ΨM.obj A)) (ακ.app (L₀X.obj A)) (ΨG.map (cc.hom.app A)) hx g g' hk he

section LiftExchange

variable {ℓ : ℕ} [Fact ℓ.Prime] {k₁ k₁' k₂ k₂' : Type u} [Field k₁] [Field k₁'] [Field k₂]
  [Field k₂'] {X : Over (Spec (.of k₁))} {X' : Over (Spec (.of k₁'))} {Y : Over (Spec (.of k₂))}
  {Y' : Over (Spec (.of k₂'))} {M : NearbyCyclesModel X.left X'.left}
  {N : NearbyCyclesModel Y.left Y'.left} {j : Y.left ⟶ X.left} {j' : Y'.left ⟶ X'.left}

/-- **Averaging splittings on bounded constructible complexes**: let `β` be the restriction
`NearbyCyclesModel.liftExchange` of an exchange `α : Ψ_M ⋙ Lj'^* ⟶ Lj^* ⋙ Ψ_N` to bounded
constructible complexes, and `ρ σ` the restrictions of the actions of self-maps `ψ σ` of `N`
indexed by a group `G`, multiplicative and trivial on a normal subgroup `U` of finite index at
`Lj^* A`. If `α` is split at `A` by `r` with `[G : U] • (r ≫ α) = ∑ ρ(ψ σ)` over representatives
of `G ⧸ U`, then so is `β`, and the representatives of `a⁻¹` and `a` act inversely. -/
private lemma exists_retraction_liftExchange_of_averaging
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (α : M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        L((j')^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (β : boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') j' ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) j ⋙
        boundedConstructibleNearbyCycles hN)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) α
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ j' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ j K.obj K.property))
    {G : Type*} [Group G] (ψ : G → N.Hom N (𝟙 _) (𝟙 _))
    (ρ : G → (boundedConstructibleNearbyCycles hN ⟶ boundedConstructibleNearbyCycles hN))
    (hρ : ∀ σ K, (ρ σ).app K =
      ObjectProperty.homMk ((ψ σ).autAction (Profinite.padicAlgClRingObj ℓ) K.obj))
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (U : Subgroup G) [U.Normal]
    [Fintype (G ⧸ U)]
    (hmul : ∀ σ τ : G, (ψ (σ * τ)).autAction (Profinite.padicAlgClRingObj ℓ)
        (L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj) =
      (ψ τ).autAction (Profinite.padicAlgClRingObj ℓ)
          (L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj) ≫
        (ψ σ).autAction (Profinite.padicAlgClRingObj ℓ)
          (L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj))
    (htriv : ∀ σ ∈ U, (ψ σ).autAction (Profinite.padicAlgClRingObj ℓ)
        (L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj) = 𝟙 _)
    {r : (L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        A.obj ⟶ (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
          L((j')^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A.obj}
    (hr : α.app A.obj ≫ r = 𝟙 _)
    (hravg : Fintype.card (G ⧸ U) • (r ≫ α.app A.obj) =
      ∑ σ : G ⧸ U, (ψ σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
        (L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj)) :
    ∃ r' : (boundedConstructibleNearbyCycles hN).obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) j).obj A) ⟶
      (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') j').obj
        ((boundedConstructibleNearbyCycles hM).obj A),
      β.app A ≫ r' = 𝟙 _ ∧
      Fintype.card (G ⧸ U) • (r' ≫ β.app A) = ∑ σ : G ⧸ U, (ρ σ.out).app _ ∧
      ∀ a : G ⧸ U, (ρ a⁻¹.out).app ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y)
          j).obj A) ≫ (ρ a.out).app ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y)
          j).obj A) = 𝟙 _ := by
  subst hβ
  refine ⟨ObjectProperty.homMk r, ObjectProperty.hom_ext _ hr, ?_, fun a ↦ ?_⟩
  · apply (ObjectProperty.ι _).map_injective
    rw [Functor.map_nsmul, Functor.map_sum]
    simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
      liftExchange_app_hom, ObjectProperty.homMk_hom, hρ]
    exact hravg
  · have hmem : a.out * a⁻¹.out ∈ U := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.out_eq',
        QuotientGroup.out_eq', mul_inv_cancel]
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, hρ, hρ, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.id_hom]
    exact (hmul _ _).symm.trans (htriv _ hmem)

end LiftExchange

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfGenericBase

section Ambient

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- Triviality of a base-change action passes through the invertible exchange to the slice. -/
private lemma genericSliceAut_autAction_eq_id_of_baseChange
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₁.left)))
    (σ : GenericAut k' (traitSliceField k'))
    (hσ : (baseChangeAut h.isTraitModelOver b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
        (L((𝟙 X₁.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) = 𝟙 _) :
    (genericSliceAut (traitSliceCoord k') hb σ).autAction (Profinite.padicAlgClRingObj ℓ)
      (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) =
        𝟙 _ := by
  have hc := h.genericSliceModel_ε_comp_genericSliceBaseMap (traitSliceCoord k') hb
  have hk := isIso_pullbackExchange_genericSliceToBaseChange (traitSliceCoord k')
    h.isTraitModelOver hb (Profinite.padicAlgClRingObj ℓ) hc
  have := NatIso.isIso_app_of_isIso ((genericSliceToBaseChange (traitSliceCoord k')
    h.isTraitModelOver hb hc).pullbackExchange (Profinite.padicAlgClRingObj ℓ))
    (L((𝟙 X₁.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)
  refine eq_id_of_naturality_of_iso _ (fun f ↦ Hom.autAction_naturality _ _ f)
    ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
      (Category.comp_id (h.genericSliceBaseMap (traitSliceCoord k') hb))).app A) ?_
  exact eq_id_of_comp_eq_map_comp _ _ _ hσ
    (pullbackExchange_genericSliceToBaseChange_app_comp_autAction (traitSliceCoord k')
      h.isTraitModelOver hb (Profinite.padicAlgClRingObj ℓ) hc σ
      (L((𝟙 X₁.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A))

/-- **The slice exchange is an averaging summand** (ambient derived categories): for a bounded
constructible `A` on `X₁`, there is a subgroup `V` of finite index of the pro-`p` kernel `P'`
acting trivially on `Ψ_{M''} (c^* A)`, and for every subgroup `U ≤ V` of finite index, the
pullback exchange `α : p^* Ψ_M A ⟶ Ψ_{M''} (c^* A)` of the projection from the generic slice
model is split, with `[P' : U]` times its idempotent the sum of the actions of representatives of
`P' ⧸ U`. Deduced from the same statement for the base change `M_b`
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`): the projection
`M'' ⟶ M` is the composite of the morphism `κ : M'' ⟶ M_b` with identity components
(`NearbyCyclesModel.genericSliceToBaseChange`) and of the projection `M_b ⟶ M`. -/
private theorem exists_subgroup_genericSliceHom_pullbackExchange
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₁.left)))
    (hA : boundedConstructible _ A) :
    ∃ V : Subgroup (GenericAut k' (traitSliceField k')), V.FiniteIndex ∧
      (∀ σ ∈ V, (genericSliceAut (traitSliceCoord k') hb σ).autAction
          (Profinite.padicAlgClRingObj ℓ)
          (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            A) = 𝟙 _) ∧
      ∀ U : Subgroup (GenericAut k' (traitSliceField k')), U ≤ V →
        ∀ _ : Fintype (GenericAut k' (traitSliceField k') ⧸ U),
        ∃ r, ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A ≫ r = 𝟙 _ ∧
          Fintype.card (GenericAut k' (traitSliceField k') ⧸ U) •
              (r ≫ ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange
                (Profinite.padicAlgClRingObj ℓ)).app A) =
            ∑ σ : GenericAut k' (traitSliceField k') ⧸ U,
              (genericSliceAut (traitSliceCoord k') hb σ.out).autAction
                (Profinite.padicAlgClRingObj ℓ)
                (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦
                  Profinite.padicAlgClRingObj ℓ⟧).obj A) := by
  have hA' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A hA
  have hM := h.isTraitModelOver
  have hD := exists_subgroup_pullbackExchange_baseChangeHom_traitSlice (ℓ := ℓ)
    hM hb (A := A)
  refine (h.exists_extension_total (Profinite.padicAlgClRingObj ℓ) hA).elim fun B hB ↦ ?_
  have hD2 := hD hA' hB.1 hB.2.some
  obtain ⟨V, hV, htriv, rB, hrB, havgB⟩ := hD2
  have hc := h.genericSliceModel_ε_comp_genericSliceBaseMap (traitSliceCoord k') hb
  refine ⟨V, Subgroup.finiteIndex_of_finite_quotient,
    fun σ hσ ↦ genericSliceAut_autAction_eq_id_of_baseChange ℓ h hb A σ (htriv σ hσ),
    fun U hUV _ ↦ ?_⟩
  have hs := sum_autAction_baseChangeAut_eq_relIndex_nsmul hM b hb
    (traitSlice (traitSliceCoord k')) (traitSlice_over _) (Profinite.padicAlgClRingObj ℓ) hUV
    _ htriv
  have hn : Fintype.card (GenericAut k' (traitSliceField k') ⧸ U) =
      U.relIndex V * Fintype.card (GenericAut k' (traitSliceField k') ⧸ V) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Subgroup.index,
      ← Subgroup.index, Subgroup.relIndex_mul_index hUV]
  -- the projection `M'' ⟶ M` is `κ` followed by the projection `M_b ⟶ M`
  have hspec : 𝟙 _ ≫ baseChangeSpecialMap hM b hb
      (traitSlice (traitSliceCoord k')) (traitSlice_over _) =
        sliceSpecialMap (traitSliceCoord k') hM hb := by
    rw [Category.id_comp]
    apply hM.isPullback_i.hom_ext <;>
      simp [sliceSpecialMap, baseChangeSpecialMap]
  have htot : (genericSliceToBaseChange (traitSliceCoord k') hM hb hc).total ≫
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over _)).total = (h.genericSliceHom (traitSliceCoord k') hb).total := by
    simp [genericSliceHom]
  have hgen : (genericSliceToBaseChange (traitSliceCoord k') hM hb hc).generic ≫
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over _)).generic = (h.genericSliceHom (traitSliceCoord k') hb).generic := by
    simp [genericSliceHom]
  have hk := isIso_pullbackExchange_genericSliceToBaseChange (traitSliceCoord k')
    hM hb (Profinite.padicAlgClRingObj ℓ) hc
  have hx := (genericSliceToBaseChange (traitSliceCoord k') hM hb
    hc).pullbackExchange_comp_app_of_eq (Profinite.padicAlgClRingObj ℓ)
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _))
    (h.genericSliceHom (traitSliceCoord k') hb) (Category.comp_id _) hspec htot hgen A
  have key := exists_retraction_of_averaging_comp (ι := GenericAut k' (traitSliceField k') ⧸ U)
    ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange (Profinite.padicAlgClRingObj ℓ))
    ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ))
    ((genericSliceToBaseChange (traitSliceCoord k') hM hb hc).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ))
    (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hspec)
    (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
      (Category.comp_id (h.genericSliceBaseMap (traitSliceCoord k') hb)))
    (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ)
      (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left) A
    (by exact_mod_proofs hx) (by infer_instance) rB (by exact_mod_proofs hrB) Finset.univ
    (Fintype.card (GenericAut k' (traitSliceField k') ⧸ U))
    (fun σ : GenericAut k' (traitSliceField k') ⧸ U ↦ (baseChangeAut hM b hb
      (traitSlice (traitSliceCoord k')) (traitSlice_over _) σ.out).autAction
        (Profinite.padicAlgClRingObj ℓ) _)
    (U.relIndex V) (Fintype.card (GenericAut k' (traitSliceField k') ⧸ V)) hn _
    (by exact_mod_proofs hs) (by exact_mod_proofs havgB)
    (fun σ : GenericAut k' (traitSliceField k') ⧸ U ↦
      (genericSliceAut (traitSliceCoord k') hb σ.out).autAction (Profinite.padicAlgClRingObj ℓ) _)
    (fun σ ↦ (genericSliceAut (traitSliceCoord k') hb σ.out).autAction
      (Profinite.padicAlgClRingObj ℓ) _)
    (fun σ ↦ pullbackExchange_genericSliceToBaseChange_app_comp_autAction
      (traitSliceCoord k') hM hb (Profinite.padicAlgClRingObj ℓ) hc σ.out _)
    (fun σ ↦ Hom.autAction_naturality _ _ _)
  obtain ⟨r, hr₁, hr₂⟩ := key
  exact ⟨r, by exact_mod_proofs hr₁, by exact_mod_proofs hr₂⟩

end Ambient

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- **The slice exchange is an averaging summand** (bounded constructible complexes): for a bounded
constructible `A` on `X₁` there is a subgroup `V` of finite index of the pro-`p` kernel `P'` such
that for every normal subgroup `U ≤ V` of finite index, the slice exchange
`α_A : p^* Ψ_M A ⟶ Ψ_{M''} c^* A` is split by some `r` with `[P' : U] • (r ≫ α_A)` the sum of the
actions (`NearbyCyclesModel.genericSliceAut`) of representatives of the elements of `P' ⧸ U`, and
these actions are invertible, the representative of `a⁻¹` acting inversely to that of `a`.
The bounded constructible form of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_subgroup_genericSliceHom_pullbackExchange`. -/
private theorem exists_subgroup_genericSliceExchange
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ V : Subgroup (GenericAut k' (traitSliceField k')), V.FiniteIndex ∧
      ∀ (U : Subgroup (GenericAut k' (traitSliceField k'))) (_ : U.Normal)
        (_ : Fintype (GenericAut k' (traitSliceField k') ⧸ U)), U ≤ V →
        ∃ r : (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
            ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ⟶
          (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj
            ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj A),
          (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A ≫ r = 𝟙 _ ∧
          Fintype.card (GenericAut k' (traitSliceField k') ⧸ U) •
              (r ≫ (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A) =
            ∑ a : GenericAut k' (traitSliceField k') ⧸ U,
              (genericSliceSelfAction (traitSliceCoord k') ℓ h hb
                (genericSliceAut (traitSliceCoord k') hb a.out)).app _ ∧
          ∀ a : GenericAut k' (traitSliceField k') ⧸ U,
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb
                (genericSliceAut (traitSliceCoord k') hb a⁻¹.out)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ≫
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb
                (genericSliceAut (traitSliceCoord k') hb a.out)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) = 𝟙 _ := by
  have hD := exists_subgroup_genericSliceHom_pullbackExchange ℓ h hb A.obj A.property
  obtain ⟨V, hV, htriv, havg⟩ := hD
  refine ⟨V, hV, fun U _ _ hUV ↦ ?_⟩
  have hU := havg U hUV inferInstance
  obtain ⟨r, hr, hravg⟩ := hU
  exact exists_retraction_liftExchange_of_averaging
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
      h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ))
    (h.preservesBoundedConstructible (ℓ := ℓ))
    ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange (Profinite.padicAlgClRingObj ℓ))
    (genericSliceExchange (traitSliceCoord k') ℓ h hb) rfl (genericSliceAut (traitSliceCoord k') hb)
    (fun σ ↦ genericSliceSelfAction (traitSliceCoord k') ℓ h hb
      (genericSliceAut (traitSliceCoord k') hb σ))
    (fun σ K ↦ genericSliceSelfAction_app (traitSliceCoord k') ℓ h hb _ K) A U
    (fun σ τ ↦ autAction_genericSliceAut_mul (traitSliceCoord k') hb _ σ τ _)
    (fun σ hσ ↦ htriv σ (hUV hσ)) hr hravg

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` in the users of the
-- following statement.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-- **The slice exchange is an averaging summand at a finite level** (blueprint
`lemma-nearby-duality-slice--1`, the generic-slicing identification `g_s^* Ψ_M ≃ (Ψ_{M''} c^*)^P`,
with `lemma-duality-invariants-pro-p--1`; SGA 4½, [Th. finitude], §3). For two bounded constructible
complexes `A₁`, `A₂` on `X₁`, the pro-`p` kernel `P` of the map of inertia groups acts on
`Ψ_{M''} c^* A₁` and `Ψ_{M''} c^* A₂` through a finite quotient `Γ`: there are automorphisms
`ψ a` of the generic slice model, the identity on the total space, which act on the geometric
generic point `Spec Ω_K` through automorphisms `σ` over the generic point `η_K` of `Spec K⟦t⟧`
(the elements of `P` act through `Gal(Ω_K/η_K)`), lifting the elements `a ∈ Γ`, such that
`α_{Aᵢ}` is split by `rᵢ`
with `|Γ| • (rᵢ ≫ α_{Aᵢ}) = ∑ₐ ρ(ψ a)` and `ρ(ψ a⁻¹)` inverse to `ρ(ψ a)` on `Ψ_{M''} c^* Aᵢ`.
The order of `Γ` is invertible, the coefficients being `ℚ̄_ℓ`.

`Γ` is the quotient of the group of generic automorphisms by the normal core `N` of the
intersection of the subgroups `Vᵢ` of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_subgroup_genericSliceExchange` for `A₁` and
`A₂`, and `ψ a` is the action (`NearbyCyclesModel.genericSliceAut`) of a representative of `a`. -/
theorem exists_averaging_genericSliceExchange
    (A₁ A₂ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (Γ : Type u) (_ : Group Γ) (_ : Fintype Γ)
      (ψ : Γ → (genericSliceModel (traitSliceCoord k') hb).Hom
        (genericSliceModel (traitSliceCoord k') hb) (𝟙 _) (𝟙 _)),
      (∀ a, (ψ a).total = 𝟙 _ ∧ IsIso (ψ a).generic ∧
        ∃ σ : Spec (.of (traitGenericField (traitSliceField k'))) ⟶
            Spec (.of (traitGenericField (traitSliceField k'))),
          σ ≫ traitGenericPointToSpec (traitSliceField k') =
              traitGenericPointToSpec (traitSliceField k') ∧
            (ψ a).generic ≫ pullback.snd _ _ = pullback.snd _ _ ≫ σ) ∧
      (∀ T : Dᵇc((baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left)⟦
        Profinite.padicAlgClRingObj ℓ⟧, IsIso (Fintype.card Γ • 𝟙 T)) ∧
      ∀ A, (A = A₁ ∨ A = A₂) →
        ∃ r : (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
            ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ⟶
          (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj
            ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj A),
          (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A ≫ r = 𝟙 _ ∧
          Fintype.card Γ • (r ≫ (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A) =
            ∑ a, (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a)).app _ ∧
          ∀ a, (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a⁻¹)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ≫
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) = 𝟙 _ := by
  have hD₁ := exists_subgroup_genericSliceExchange ℓ h hb A₁
  have hD₂ := exists_subgroup_genericSliceExchange ℓ h hb A₂
  obtain ⟨V₁, hV₁, h₁⟩ := hD₁
  obtain ⟨V₂, hV₂, h₂⟩ := hD₂
  let N := (V₁ ⊓ V₂).normalCore
  let _ : Fintype (GenericAut k' (traitSliceField k') ⧸ N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  have hN₁ : N ≤ V₁ := (Subgroup.normalCore_le _).trans inf_le_left
  have hN₂ : N ≤ V₂ := (Subgroup.normalCore_le _).trans inf_le_right
  refine ⟨GenericAut k' (traitSliceField k') ⧸ N, inferInstance, inferInstance,
    fun a ↦ genericSliceAut (traitSliceCoord k') hb a.out, fun a ↦ ⟨rfl, inferInstance, a.out.τ,
      a.out.τ_comp_traitGenericPointToSpec, genericSliceAut_generic_snd _ _ _⟩, fun T ↦ ?_, ?_⟩
  · have : IsIso ((ObjectProperty.ι _).map
        (Fintype.card (GenericAut k' (traitSliceField k') ⧸ N) • 𝟙 T)) := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      exact isIso_nsmul_id_derived_padicAlgClRingObj ℓ _ Fintype.card_ne_zero _
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  rintro A (rfl | rfl)
  · exact h₁ N inferInstance _ hN₁
  · exact h₂ N inferInstance _ hN₂

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
