/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux

/-!

# Restriction of models to opens of the total space

Let `N` be a model of `Y` with special fibre `Y'` (`AlgebraicGeometry.ProEtale.CondensedRing.
NearbyCyclesModel`) and `V` an open of its total space. The *restriction* of `N` to `V`
(`NearbyCyclesModel.restrictOpens`) has total space `V`, geometric generic fibre `𝒳_η̄ ×_𝒳 V` and
special fibre `Y' ×_𝒳 V`; it maps to `N` by the open immersion of total spaces
(`NearbyCyclesModel.restrictOpensHom`), whose pullback exchange is invertible
(`NearbyCyclesModel.isIso_restrictOpensHom_pullbackExchange`). A morphism of models
`φ : M ⟶ N` restricts to a morphism `φ|_V : M|_{φ⁻¹ V} ⟶ N|_V`
(`NearbyCyclesModel.Hom.restrictOpens`) commuting with these open immersions.

## Main results

- `NearbyCyclesModel.Hom.isIso_toGeneric_pullbackExchange_app_of_restrictOpens`: **the
  invertibility of the pullback exchange of the models of the geometric generic fibres is local on
  the total space**. If every point `x` of the special fibre of `M` has an open neighbourhood `V`
  of `φ(x)` such that the pullback exchange of `φ|_V` is invertible at the restriction of `K`,
  then the pullback exchange of `φ` is invertible at `K`. Indeed by the square law of the
  pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_square`) and the invertibility of
  the exchanges of open immersions, the restriction of the exchange of `φ` to the open
  `M.i⁻¹(φ⁻¹ V)` of the special fibre is identified with the exchange of `φ|_V`
  (`NearbyCyclesModel.Hom.isIso_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens`),
  and these opens cover the special fibre.
- `NearbyCyclesModel.isPullback_restrictOpens_j`, `NearbyCyclesModel.isPullback_restrictOpens_i`,
  `NearbyCyclesModel.Hom.isPullback_restrictOpens_total`: cartesian squares of fibres over a trait
  and of total spaces over a change of trait restrict to opens.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A morphism of complexes of module objects is invertible as soon as every point has an open
neighbourhood, given by an open immersion `u`, such that its derived pullback along `u` is
invertible: the open immersions form a pro-étale cover. -/
theorem isIso_of_forall_exists_isIso_leftDerivedUpperStar_map_of_isOpenImmersion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {K K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (α : K ⟶ K')
    (h : ∀ x : X, ∃ (U : Scheme.{u}) (u : U ⟶ X), IsOpenImmersion u ∧ x ∈ Set.range u ∧
      IsIso ((L((u)^*⟦Λ⟧)).map α)) : IsIso α := by
  choose U u hu hx hα using h
  exact isIso_of_forall_isIso_leftDerivedUpperStar_map
    ((Scheme.Cover.mkOfCovers X U u (fun x ↦ ⟨x, hx x⟩) hu).weaken
      Scheme.zariskiPrecoverage_le_proetalePrecoverage) α hα

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}}

/-! ### Restriction of a model to an open of the total space -/

/-- The *restriction* of a model `N` to an open `V` of its total space: total space `V`,
geometric generic fibre `𝒳_η̄ ×_𝒳 V` and special fibre `Y' ×_𝒳 V`. -/
noncomputable abbrev restrictOpens (N : NearbyCyclesModel Y Y') (V : N.total.Opens) :
    NearbyCyclesModel Y (pullback N.i V.ι) where
  total := V
  generic := pullback N.j V.ι
  j := pullback.snd _ _
  i := pullback.snd _ _
  ε := pullback.fst _ _ ≫ N.ε

/-- The open immersion of models `N|_V ⟶ N` of the restriction of a model to an open of its total
space. -/
noncomputable abbrev restrictOpensHom (N : NearbyCyclesModel Y Y') (V : N.total.Opens) :
    (N.restrictOpens V).Hom N (𝟙 Y) (pullback.fst N.i V.ι) where
  total := V.ι
  generic := pullback.fst _ _
  comm_j := pullback.condition
  comm_i := pullback.condition
  comm_ε := (Category.comp_id _).symm

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback exchange of the open immersion `N|_V ⟶ N` is invertible. -/
theorem isIso_restrictOpensHom_pullbackExchange (N : NearbyCyclesModel Y Y')
    (V : N.total.Opens) : IsIso ((N.restrictOpensHom V).pullbackExchange Λ) :=
  (N.restrictOpensHom V).isIso_pullbackExchange_of_isOpenImmersion Λ
    (IsPullback.of_hasPullback _ _)

/-- The pullback exchange of the open immersion `N|_V ⟶ N`, on the models of the geometric generic
fibres, is invertible. -/
theorem isIso_restrictOpensHom_toGeneric_pullbackExchange (N : NearbyCyclesModel Y Y')
    (V : N.total.Opens) : IsIso ((N.restrictOpensHom V).toGeneric.pullbackExchange Λ) :=
  (N.restrictOpensHom V).toGeneric.isIso_pullbackExchange_of_isOpenImmersion Λ
    (IsPullback.of_hasPullback _ _)

/-! ### Restriction of a morphism of models -/

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The *restriction* `φ|_V : M|_{φ⁻¹ V} ⟶ N|_V` of a morphism of models to an open `V` of the
total space of the target. -/
noncomputable abbrev Hom.restrictOpens (φ : M.Hom N f f') (V : N.total.Opens) :
    (M.restrictOpens (φ.total ⁻¹ᵁ V)).Hom (N.restrictOpens V) f
      (pullback.map _ _ _ _ f' (φ.total ∣_ V) φ.total φ.comm_i.symm
        (morphismRestrict_ι _ _).symm) where
  total := φ.total ∣_ V
  generic := pullback.map _ _ _ _ φ.generic (φ.total ∣_ V) φ.total φ.comm_j.symm
    (morphismRestrict_ι _ _).symm
  comm_j := pullback.lift_snd _ _ _
  comm_i := pullback.lift_snd _ _ _
  comm_ε := by simp [φ.comm_ε]

namespace Hom

variable (φ : M.Hom N f f') (V : N.total.Opens)

/-- The restriction of a morphism of models commutes with the open immersions of the
restrictions, on total spaces. -/
lemma restrictOpens_total_comp :
    (φ.restrictOpens V).total ≫ (N.restrictOpensHom V).total =
      (M.restrictOpensHom (φ.total ⁻¹ᵁ V)).total ≫ φ.total :=
  morphismRestrict_ι _ _

/-- The restriction of a morphism of models commutes with the open immersions of the
restrictions, on geometric generic fibres. -/
lemma restrictOpens_generic_comp :
    (φ.restrictOpens V).generic ≫ (N.restrictOpensHom V).generic =
      (M.restrictOpensHom (φ.total ⁻¹ᵁ V)).generic ≫ φ.generic :=
  pullback.lift_fst _ _ _

/-- The restriction of a morphism of models commutes with the open immersions of the
restrictions, on special fibres. -/
lemma restrictOpens_special_comp :
    pullback.map _ _ _ _ f' (φ.total ∣_ V) φ.total φ.comm_i.symm (morphismRestrict_ι _ _).symm ≫
      pullback.fst N.i V.ι = pullback.fst M.i (φ.total ⁻¹ᵁ V).ι ≫ f' :=
  pullback.lift_fst _ _ _

/-! ### Locality of the pullback exchange on the total space -/

/-- If `a ≫ b ≫ c = d ≫ e ≫ g` with `a`, `b`, `e`, `g` invertible and `F.map c` invertible, then
`F.map d` is invertible. -/
private lemma isIso_map_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x₀ x₁ x₂ x₃ y₁ y₂ : C} {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₂ ⟶ x₃} {d : x₀ ⟶ y₁}
    {e : y₁ ⟶ y₂} {g : y₂ ⟶ x₃} (w : a ≫ b ≫ c = d ≫ e ≫ g) [IsIso a] [IsIso b] [IsIso e]
    [IsIso g] (hc : IsIso (F.map c)) : IsIso (F.map d) := by
  have : IsIso (F.map d ≫ F.map e ≫ F.map g) := by
    rw [← F.map_comp, ← F.map_comp, ← w, F.map_comp, F.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map e ≫ F.map g)

/-- **The pullback exchange of a restriction**: for any functor `F` on the derived category of the
special fibre `M.i⁻¹(φ⁻¹ V)` of `M|_{φ⁻¹ V}`, if `F` of the pullback exchange of `φ|_V` (on the
models of the geometric generic fibres) at the restriction of `K` is invertible, so is `F` of
the restriction to `M.i⁻¹(φ⁻¹ V)` of the pullback exchange of `φ` at `K`. This is the square law
of the pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_square`) for `φ|_V`, `φ` and
the open immersions of the restrictions, whose exchanges are invertible. -/
theorem isIso_map_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    {𝒟 : Type*} [Category 𝒟]
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback M.i (φ.total ⁻¹ᵁ V).ι))
      Ab.{u + 1}) (condensedRingObj Λ (pullback M.i (φ.total ⁻¹ᵁ V).ι))) ⥤ 𝒟)
    (H : IsIso (F.map (((φ.restrictOpens V).toGeneric.pullbackExchange Λ).app
      (L(((N.restrictOpensHom V).generic)^*⟦Λ⟧).obj K)))) :
    IsIso (F.map (L((pullback.fst M.i (φ.total ⁻¹ᵁ V).ι)^*⟦Λ⟧).map
      ((φ.toGeneric.pullbackExchange Λ).app K))) := by
  have := isIso_restrictOpensHom_toGeneric_pullbackExchange Λ N V
  have := isIso_restrictOpensHom_toGeneric_pullbackExchange Λ M (φ.total ⁻¹ᵁ V)
  have w := pullbackExchange_square Λ
    (φ.restrictOpens V).toGeneric (N.restrictOpensHom V).toGeneric
    (M.restrictOpensHom (φ.total ⁻¹ᵁ V)).toGeneric
    φ.toGeneric (φ.restrictOpens_total_comp V) (φ.restrictOpens_generic_comp V)
    (φ.restrictOpens_generic_comp V) (φ.restrictOpens_special_comp V) K
  exact isIso_map_of_comp_eq F w H

/-- **The pullback exchange of a restriction**: if the pullback exchange of `φ|_V` (on the models
of the geometric generic fibres) at the restriction of `K` is invertible, so is the restriction to
the open `M.i⁻¹(φ⁻¹ V)` of the special fibre of the pullback exchange of `φ` at `K`. -/
theorem isIso_leftDerivedUpperStar_fst_map_pullbackExchange_app_of_restrictOpens
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    (H : IsIso (((φ.restrictOpens V).toGeneric.pullbackExchange Λ).app
      (L(((N.restrictOpensHom V).generic)^*⟦Λ⟧).obj K))) :
    IsIso (L((pullback.fst M.i (φ.total ⁻¹ᵁ V).ι)^*⟦Λ⟧).map
      ((φ.toGeneric.pullbackExchange Λ).app K)) :=
  φ.isIso_map_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens Λ V K (𝟭 _) H

/-- **The pullback exchange of a restriction, after any further pullback**: for
`h : W ⟶ M.i⁻¹(φ⁻¹ V)`, if `Lh^*` of the pullback exchange of `φ|_V` (on the models of the
geometric generic fibres) at the restriction of `K` is invertible, so is the pullback along
`h ≫ u` of the pullback exchange of `φ` at `K`, where `u : M.i⁻¹(φ⁻¹ V) ⟶ X'` is the open
immersion. -/
theorem isIso_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    {W : Scheme.{u}} (h : W ⟶ pullback M.i (φ.total ⁻¹ᵁ V).ι)
    (H : IsIso (L((h)^*⟦Λ⟧).map (((φ.restrictOpens V).toGeneric.pullbackExchange Λ).app
      (L(((N.restrictOpensHom V).generic)^*⟦Λ⟧).obj K)))) :
    IsIso (L((h ≫ pullback.fst M.i (φ.total ⁻¹ᵁ V).ι)^*⟦Λ⟧).map
      ((φ.toGeneric.pullbackExchange Λ).app K)) := by
  rw [NatIso.isIso_map_iff (leftDerivedUpperStarComp Λ h _)]
  exact φ.isIso_map_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens Λ V K _ H

/-- **The invertibility of the pullback exchange is local on the total space**: if every point
`x` of the special fibre of `M` has an open neighbourhood `V` of `φ(x)` in the total space of `N`
such that the pullback exchange of `φ|_V : M|_{φ⁻¹ V} ⟶ N|_V` (on the models of the geometric
generic fibres) is invertible at the restriction of `K`, then the pullback exchange of `φ` is
invertible at `K`: its restrictions to the opens `M.i⁻¹(φ⁻¹ V)`, which cover the special fibre,
are invertible
(`NearbyCyclesModel.Hom.isIso_leftDerivedUpperStar_fst_map_pullbackExchange_app_of_restrictOpens`).
-/
theorem isIso_toGeneric_pullbackExchange_app_of_restrictOpens
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    (H : ∀ x : X', ∃ V : N.total.Opens, φ.total (M.i x) ∈ V ∧
      IsIso (((φ.restrictOpens V).toGeneric.pullbackExchange Λ).app
        (L(((N.restrictOpensHom V).generic)^*⟦Λ⟧).obj K))) :
    IsIso ((φ.toGeneric.pullbackExchange Λ).app K) := by
  refine isIso_of_forall_exists_isIso_leftDerivedUpperStar_map_of_isOpenImmersion Λ _
    fun x ↦ ?_
  obtain ⟨V, hxV, hV⟩ := H x
  refine ⟨_, pullback.fst M.i (φ.total ⁻¹ᵁ V).ι, inferInstance, ?_,
    φ.isIso_leftDerivedUpperStar_fst_map_pullbackExchange_app_of_restrictOpens Λ V K hV⟩
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  exact hxV

end Hom

/-! ### Cartesian squares over traits restrict to opens -/

section IsPullback

variable {S T : Scheme.{u}}

/-- If the geometric generic fibre of a model is cartesian over a point `t : T ⟶ S` of a base
along `q : 𝒳 ⟶ S`, so is that of its restriction to an open `V`, along `V ⟶ 𝒳 ⟶ S`. -/
lemma isPullback_restrictOpens_j (N : NearbyCyclesModel Y Y') (V : N.total.Opens)
    {q : N.total ⟶ S} {g : N.generic ⟶ T} {t : T ⟶ S} (hNj : IsPullback N.j g q t) :
    IsPullback (N.restrictOpens V).j (pullback.fst _ _ ≫ g) (V.ι ≫ q) t :=
  (IsPullback.of_hasPullback N.j V.ι).flip.paste_vert hNj

/-- If the special fibre of a model is cartesian over a point `t : T ⟶ S` of a base along
`q : 𝒳 ⟶ S`, so is that of its restriction to an open `V`, along `V ⟶ 𝒳 ⟶ S`. -/
lemma isPullback_restrictOpens_i (N : NearbyCyclesModel Y Y') (V : N.total.Opens)
    {q : N.total ⟶ S} {p : Y' ⟶ T} {t : T ⟶ S} (hNi : IsPullback N.i p q t) :
    IsPullback (N.restrictOpens V).i (pullback.fst _ _ ≫ p) (V.ι ≫ q) t :=
  (IsPullback.of_hasPullback N.i V.ι).flip.paste_vert hNi

variable {S₁ S₂ : Scheme.{u}} (φ : M.Hom N f f') (V : N.total.Opens)

/-- If the square of total spaces of a morphism of models over a change of base `s : S₂ ⟶ S₁` is
cartesian, so is that of its restriction to an open `V`. -/
lemma Hom.isPullback_restrictOpens_total {q₁ : N.total ⟶ S₁} {q₂ : M.total ⟶ S₂}
    {s : S₂ ⟶ S₁} (hφ : IsPullback φ.total q₂ q₁ s) :
    IsPullback (φ.restrictOpens V).total ((φ.total ⁻¹ᵁ V).ι ≫ q₂) (V.ι ≫ q₁) s :=
  (isPullback_morphismRestrict φ.total V).paste_vert hφ

/-- The compatibility of the geometric generic fibres of a morphism of models with maps to
`T₁`, `T₂` over `c : T₂ ⟶ T₁` restricts to opens. -/
lemma Hom.restrictOpens_generic_comp_eq {T₁ T₂ : Scheme.{u}} {g₁ : N.generic ⟶ T₁}
    {g₂ : M.generic ⟶ T₂} {c : T₂ ⟶ T₁} (hgen : φ.generic ≫ g₁ = g₂ ≫ c) :
    (φ.restrictOpens V).generic ≫ pullback.fst _ _ ≫ g₁ = (pullback.fst _ _ ≫ g₂) ≫ c := by
  simp [hgen]

/-- The compatibility of the special fibres of a morphism of models with maps to `T₁`, `T₂` over
`d : T₂ ⟶ T₁` restricts to opens. -/
lemma Hom.restrictOpens_special_comp_eq {T₁ T₂ : Scheme.{u}} {p₁ : Y' ⟶ T₁} {p₂ : X' ⟶ T₂}
    {d : T₂ ⟶ T₁} (hs : f' ≫ p₁ = p₂ ≫ d) :
    pullback.map _ _ _ _ f' (φ.total ∣_ V) φ.total φ.comm_i.symm (morphismRestrict_ι _ _).symm ≫
      pullback.fst _ _ ≫ p₁ = (pullback.fst _ _ ≫ p₂) ≫ d := by
  simp [hs]

end IsPullback

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
