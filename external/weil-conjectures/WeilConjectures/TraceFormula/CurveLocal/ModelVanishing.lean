/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.Model
public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalVanishing
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import WeilConjectures.RingTheory.StrictlyHenselianQuotient

/-!

# Vanishing of the middle terms in the strictly local model

In the strictly local model `AlgebraicGeometry.Etale.CurveLocalModel` of blueprint
`lemma-vanishing-local-term-zero-stalk--1`:

- the punctured diagonal `B ∖ Y` maps into `O = T ∖ (G ∪ V)`
  (`AlgebraicGeometry.Etale.CurveLocalModel.ψ`), since in `X ×_k X` the diagonal meets the
  vertical axis `{y} × X` only inside the graph of `h`;
- for `P ≅ Lτ^*(L ⊠ K)` with `Ly^* K = 0`, the derived global sections `RΓ(T, P)` and
  `RΓ(B, b^* P)` vanish (blueprint item (ii)): `T` and `B` are strictly local, so these are
  stalks at the closed point, that is `L_ȳ ⊗ᴸ K_ȳ = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma vertical_fst : M.vertical ≫ pullback.fst M.f M.f = M.f ≫ M.y :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma vertical_snd : M.vertical ≫ pullback.snd M.f M.f = 𝟙 M.X :=
  pullback.lift_snd _ _ _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma graph_fst : M.graph ≫ pullback.fst M.f M.f = M.h :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma graph_snd : M.graph ≫ pullback.snd M.f M.f = 𝟙 M.X :=
  pullback.lift_snd _ _ _

omit [IsAlgClosed k] in
/-- On the intersection of the diagonal with the vertical axis, the vertical axis agrees with
the graph: `Δ(x) = (y, x')` forces `x = x' = y`, and `h(y) = y`. -/
lemma pullback_snd_diagonal_vertical_comp_vertical :
    pullback.snd (pullback.diagonal M.f) M.vertical ≫ M.vertical =
      pullback.snd (pullback.diagonal M.f) M.vertical ≫ M.graph := by
  have h₁ := congrArg (· ≫ pullback.fst M.f M.f)
    (pullback.condition (f := pullback.diagonal M.f) (g := M.vertical))
  have h₂ := congrArg (· ≫ pullback.snd M.f M.f)
    (pullback.condition (f := pullback.diagonal M.f) (g := M.vertical))
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, vertical_fst,
    vertical_snd, Category.comp_id] at h₁ h₂
  rw [h₂] at h₁
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, vertical_fst, graph_fst]
    conv_rhs => rw [h₁]
    rw [Category.assoc, Category.assoc, M.y_comp_h]
  · simp

omit [IsAlgClosed k] in
/-- In `X ×_k X`, the diagonal meets the vertical axis only inside the graph of `h`. -/
lemma range_diagonal_inter_range_vertical_subset :
    Set.range (pullback.diagonal M.f) ∩ Set.range M.vertical ⊆ Set.range M.graph := by
  rw [← Scheme.Pullback.range_snd_comp, pullback_snd_diagonal_vertical_comp_vertical]
  rintro _ ⟨q, rfl⟩
  exact ⟨_, rfl⟩

/-- The open complement `B ∖ Y` lies over the open complement `T ∖ V`. -/
lemma openComplement_yB_le_preimage_v : M.yB.openComplement ≤ M.b ⁻¹ᵁ M.v.openComplement := by
  intro z hz
  simp only [Scheme.Hom.openComplement, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff,
    Scheme.Hom.mem_preimage] at hz ⊢
  rintro ⟨w, hw⟩
  apply hz
  rw [Scheme.Pullback.range_snd, Set.mem_preimage, Scheme.Pullback.range_snd, Set.mem_preimage]
  refine M.range_diagonal_inter_range_vertical_subset ⟨?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · rw [← hw, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

/-- The open complement `B ∖ Y` lies over `O = T ∖ (G ∪ V)`. -/
lemma openComplement_yB_le_preimage_O : M.yB.openComplement ≤ M.b ⁻¹ᵁ M.O := by
  intro z hz
  exact ⟨M.openComplement_yB_le hz, M.openComplement_yB_le_preimage_v hz⟩

/-- The punctured diagonal `B ∖ Y ⟶ O = T ∖ (G ∪ V)`, the restriction of `b`. -/
noncomputable def ψ : M.yB.openComplement.toScheme ⟶ M.O.toScheme :=
  M.b.resLE M.O M.yB.openComplement M.openComplement_yB_le_preimage_O

@[reassoc (attr := simp)]
lemma ψ_comp_ι : M.ψ ≫ M.O.ι = M.yB.openComplement.ι ≫ M.b :=
  Scheme.Hom.resLE_comp_ι _ _

section Vanishing

/-- A point of the spectrum of a local ring which is closed is the closed point. -/
lemma _root_.IsLocalRing.eq_closedPoint_of_isClosed {R : Type*} [CommRing R] [IsLocalRing R]
    {x : PrimeSpectrum R} (hx : IsClosed {x}) : x = IsLocalRing.closedPoint R :=
  PrimeSpectrum.ext
    (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).1 hx))

/-- A point whose image under a closed immersion is closed is closed. -/
lemma _root_.AlgebraicGeometry.isClosed_singleton_of_isClosedImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] {x : X} (hx : IsClosed {i x}) : IsClosed {x} := by
  rw [i.isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton]
  exact hx

/-- A nonempty closed subscheme of the spectrum of a strictly henselian local ring has strictly
henselian local ring of global sections: it is a quotient of the ring by a proper ideal. -/
lemma _root_.AlgebraicGeometry.isStrictlyHenselianLocalRing_of_isClosedImmersion
    {R : CommRingCat.{u}} [IsStrictlyHenselianLocalRing R] {Z : Scheme.{u}} [Nonempty Z]
    (i : Z ⟶ Spec R) [IsClosedImmersion i] : IsStrictlyHenselianLocalRing Γ(Z, ⊤) := by
  have : IsStrictlyHenselianLocalRing Γ(Spec R, ⊤) :=
    .of_ringEquiv (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  obtain ⟨z⟩ := ‹Nonempty Z›
  have : Nontrivial Γ(Z, ⊤) := (Z.presheaf.germ ⊤ z trivial).hom.domain_nontrivial
  obtain ⟨_, -, -, h, -⟩ := isStrictlyHenselianLocalRing_quotient.{u, u} Γ(Spec R, ⊤)
    inferInstance (RingHom.ker i.appTop.hom)
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
  exact .of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (IsClosedImmersion.isAffine_surjective_of_isAffine i).2)


/-- The geometric point of the strict localization `T` over its closed point. -/
noncomputable def t : Spec (.of k) ⟶ M.T :=
  Spec.map (strictHenselizationEval M.diagPoint)

@[reassoc (attr := simp)]
lemma t_comp_τ : M.t ≫ M.τ = M.diagPoint :=
  spec_map_strictHenselizationEval_comp_strictLocalizationToBase _

lemma t_apply_closedPoint :
    M.t (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint (strictHenselization M.diagPoint) :=
  spec_map_strictHenselizationEval_apply_closedPoint _

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma y_comp_diagonal : M.y ≫ pullback.diagonal M.f = M.diagPoint := by
  apply pullback.hom_ext
  · simp [diagPoint]
  · simp [diagPoint]

/-- The geometric point of the diagonal `B` over the closed point. -/
noncomputable def tB : Spec (.of k) ⟶ M.B :=
  pullback.lift M.y M.t (by rw [y_comp_diagonal, t_comp_τ])

@[reassoc (attr := simp)]
lemma tB_comp_b : M.tB ≫ M.b = M.t :=
  pullback.lift_snd _ _ _

instance : IsAffine M.B :=
  isAffine_of_isAffineHom M.b

instance : Nonempty M.B :=
  ⟨M.tB (IsLocalRing.closedPoint k)⟩

instance : IsStrictlyHenselianLocalRing Γ(M.B, ⊤) :=
  isStrictlyHenselianLocalRing_of_isClosedImmersion M.b

lemma isoSpec_hom_tB_apply_closedPoint :
    (M.tB ≫ M.B.isoSpec.hom) (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint Γ(M.B, ⊤) := by
  refine IsLocalRing.eq_closedPoint_of_isClosed ?_
  refine isClosed_singleton_of_isClosedImmersion M.B.isoSpec.inv ?_
  rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine isClosed_singleton_of_isClosedImmersion M.b ?_
  rw [← Scheme.Hom.comp_apply, tB_comp_b, t_apply_closedPoint]
  exact IsLocalRing.isClosed_singleton_closedPoint _

variable {Λ : Type (u + 1)} [CommRing Λ]

omit [IsAlgClosed k] in
/-- For a `k`-point `g` of `X ×_k X` with second coordinate `y` and `Ly^* K = 0`, the pullback
`Lg^*(L ⊠ K) ≅ Lg^*Lp₁^*L ⊗ᴸ Ly^*K` vanishes. -/
lemma isZero_leftDerivedUpperStar_externalProduct (g : Spec (.of k) ⟶ pullback M.f M.f)
    (hg : g ≫ pullback.snd M.f M.f = M.y)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsZero ((L((g)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :=
  (isZero_derivedTensor_obj_obj_of_isZero_right _ (hK.of_iso
    ((leftDerivedUpperStarComp _ g (pullback.snd M.f M.f) M.y hg.symm).app K).symm)).of_iso
    (leftDerivedUpperStarTensorIso _ g _ _)

/-- For a `k`-point `g` of `T` over `(y, y)`, `P ≅ Lτ^*(L ⊠ K)` and `Ly^* K = 0`, the pullback
`Lg^* P` vanishes. -/
lemma isZero_leftDerivedUpperStar_obj (g : Spec (.of k) ⟶ M.T) (hg : g ≫ M.τ = M.diagPoint)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    IsZero ((L((g)^*[ModuleCat.{u + 1} Λ])).obj P) :=
  ((M.isZero_leftDerivedUpperStar_externalProduct (g ≫ M.τ)
    (by rw [hg, diagPoint, pullback.lift_snd]) L K hK).of_iso
    ((leftDerivedUpperStarComp _ g M.τ).app _).symm).of_iso
    ((L((g)^*[ModuleCat.{u + 1} Λ])).mapIso eP)

/-- The `Plus` version of `isZero_leftDerivedUpperStar_obj`. -/
lemma isZero_mapDerivedCategoryPlus_obj (g : Spec (.of k) ⟶ M.T) (hg : g ≫ M.τ = M.diagPoint)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    IsZero ((Functor.mapDerivedCategoryPlus (g)^*[ModuleCat.{u + 1} Λ]).obj P) :=
  IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _
    ((M.isZero_leftDerivedUpperStar_obj g hg L K hK P.obj eP).of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ g).app P.obj).symm)

/-- Blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (ii), for `T`: if `P ≅ Lτ^*(L ⊠ K)`
with `Ly^* K = 0`, then `RΓ(T, P) = 0`. -/
theorem isZero_obj₂_a
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    IsZero ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj P).obj₂ :=
  isZero_sectionsWithSupportTriangle_obj₂_of_isStrictlyHenselianLocalRing
    (R := strictHenselization M.diagPoint) M.a (Iso.refl _) M.t
    (by
      rw [Iso.refl_hom, Category.comp_id]
      exact M.t_apply_closedPoint) P
    (M.isZero_mapDerivedCategoryPlus_obj M.t M.t_comp_τ L K hK P eP)

/-- Blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (ii), for `B`: if `P ≅ Lτ^*(L ⊠ K)`
with `Ly^* K = 0`, then `RΓ(B, b^* P) = 0`. -/
theorem isZero_obj₂_yB
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    IsZero ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
      ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} Λ]).obj P)).obj₂ :=
  isZero_sectionsWithSupportTriangle_obj₂_of_isStrictlyHenselianLocalRing
    (R := Γ(M.B, ⊤)) M.yB M.B.isoSpec M.tB M.isoSpec_hom_tB_apply_closedPoint _
    (IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _
      ((M.isZero_leftDerivedUpperStar_obj (M.tB ≫ M.b) (by rw [tB_comp_b, t_comp_τ]) L K hK
        P.obj eP).of_iso
        (((leftDerivedUpperStarIsoMapDerivedCategory _ M.tB).app _ ≪≫
            (D((M.tB)^*[ModuleCat.{u + 1} Λ])).mapIso
              ((leftDerivedUpperStarIsoMapDerivedCategory _ M.b).app P.obj)).symm ≪≫
          ((leftDerivedUpperStarComp _ M.tB M.b).app P.obj).symm)))

end Vanishing

end AlgebraicGeometry.Etale.CurveLocalModel
