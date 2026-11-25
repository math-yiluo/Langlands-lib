/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceOpen
public import WeilConjectures.TraceFormula.Specialization.CoordinateCompactification
public import WeilConjectures.Tactic.TransportExact

/-!

# The twist equation of the generic slice and shrinking the base

Let `M` be a trait model over the generic base `(F, X₁, ι)`. Its *shrunk model*
`M♭ = NearbyCyclesModel.IsTraitModelOfGenericBase.shrink` has the same total space, geometric
generic fibre and inclusions, but its base is the generic fibre `𝒳_η = 𝒳 ×_S η`
(`NearbyCyclesModel.traitGenericBase`), over the generic base `(η, 𝒳_η, 𝟙)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isTraitModelOfGenericBase_shrink`). For any map
`c : 𝒳_η ⟶ X₁` through which `ε` factors, the identity of `M` is a morphism of models
`M♭ ⟶ M` over `c` (`NearbyCyclesModel.IsTraitModelOfGenericBase.shrinkHom`).

* `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_shrink`: if
  `θ_M = α ≫ Ψ_{M♭}(Φ) ≫ θ_{M♭}` for an isomorphism `Φ : c^* ω_{X₁} ≅ ω_{𝒳_η}`, the twist
  equation of the generic slice for `M♭` implies it for `M` (the generic slices of `M` and `M♭`
  are the same model), exactly as for re-basing
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_rebase`).
* `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_θ_eq_shrink_of_openSubmodel`: this
  hypothesis on `θ` holds for open sub-models `M ⊆ M_c` of proper models with proper `X_c`, `X_c'`
  and full generic fibre: `θ_M` is the restriction of `θ_{M_c}` (open restriction), which is
  re-based (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_rebase_of_isProper`) and
  restricted again to `θ_{M♭}` along the open immersion of models `M♭ ⟶ M_c'`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.shrinkRebaseHom`); the exchanges form a commutative
  square by the composition law (`NearbyCyclesModel.specialIdExchange_comp_pullbackExchange_square`)
  and the algebra is `NearbyCyclesModel.exists_θ_eq_of_openSubmodel_of_rebase`.
* `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_shrink_of_traitFibreModel`:
  `M♭` is isomorphic to the generic standard model `NearbyCyclesModel.traitFibreModel q`, so the
  twist equation passes from the latter to `M♭`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel`).
* `IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_restrictOpen_of_traitFibreModel`
  is the bridge for the restrictions `M_c|_V` of the induction: the twist equation for
  `NearbyCyclesModel.traitFibreModel (V ⟶ S)` (base equal to its generic fibre, `ι = 𝟙`, the input
  of `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification`) implies it
  for `M_c|_V`.

## Implementation notes

As in `TraceFormula.Specialization.NearbyDualityGenericBaseSliceRebaseTwist`, the ambient
identities are proved for arbitrary models and lifted by `transport_exact`. The global instances
`Fact (ringChar (FractionRing (PowerSeries k'))).Prime` must be used rather than local ones (the
two ring structures on `FractionRing` make the comparison expensive), and the generic standard
model of `V` is spelled with `T := (M_c|_V).total` so that it is syntactically the one produced
for the shrunk model of `M_c|_V`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

-- `IsSepClosed k'` gives a second instance path to the Henselian property of `k'` inside
-- `FractionRing (PowerSeries k')`, making terms elaborated with and without it expensive to unify.
attribute [-instance] AlgebraicGeometry.Scheme.isStrictlyHenselianLocalRing_of_isSepClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Abstract

/-- **The dualizing maps of an open sub-model and of its shrunk model**, abstractly: let `θ_c` be
restricted to `θ_M` along an open immersion of models (`h₁`, the exchange `α_r` invertible), let
`θ_c = ρ_c ≫ Ψ_η(φ) ≫ θ_η` (re-basing, `h₂`), let `θ_η` restrict to `θ♭` (`h₃`, same
identification `ρ'` of the special fibres) and let the exchanges be compatible (`h₄`). Then
`θ_M = ρ_ψ ≫ Ψ♭(Φ) ≫ θ♭` for `Φ = C(ρ_j⁻¹) ≪≫ E⁻¹ ≪≫ W(φ) ≪≫ ρ_w`. -/
lemma exists_θ_eq_of_openSubmodel_of_rebase {DXc DX₁ DXη DY DSc DS : Type*} [Category DXc]
    [Category DX₁] [Category DXη] [Category DY] [Category DSc] [Category DS]
    {Ψc : DXc ⥤ DSc} {ΨM : DX₁ ⥤ DS} {Ψη : DXη ⥤ DSc} {Ψb : DY ⥤ DS} {J' : DSc ⥤ DS}
    {J : DXc ⥤ DX₁} {Pπ : DXc ⥤ DXη} {W : DXη ⥤ DY} {C : DX₁ ⥤ DY}
    {ωc : DXc} {ω₁ : DX₁} {ωη : DXη} {ωY : DY} {ωs : DSc} {ω' : DS}
    (θc : Ψc.obj ωc ⟶ ωs) (θM : ΨM.obj ω₁ ⟶ ω') (θη : Ψη.obj ωη ⟶ ωs) (θb : Ψb.obj ωY ⟶ ω')
    (ρ' : J'.obj ωs ≅ ω') (ρj : J.obj ωc ≅ ω₁) (ρw : W.obj ωη ≅ ωY) (φ : Pπ.obj ωc ⟶ ωη)
    [IsIso φ] (αr : Ψc ⋙ J' ⟶ J ⋙ ΨM) [IsIso (αr.app ωc)] (αs : Ψη ⋙ J' ⟶ W ⋙ Ψb)
    (ρc : Ψc ⟶ Pπ ⋙ Ψη) (ρψ : ΨM ⟶ C ⋙ Ψb) (E : W.obj (Pπ.obj ωc) ≅ C.obj (J.obj ωc))
    (h₁ : J'.map θc ≫ ρ'.hom = αr.app ωc ≫ ΨM.map ρj.hom ≫ θM)
    (h₂ : θc = ρc.app ωc ≫ Ψη.map φ ≫ θη)
    (h₃ : J'.map θη ≫ ρ'.hom = αs.app ωη ≫ Ψb.map ρw.hom ≫ θb)
    (h₄ : J'.map (ρc.app ωc) ≫ αs.app (Pπ.obj ωc) ≫ Ψb.map E.hom =
      αr.app ωc ≫ ρψ.app (J.obj ωc)) :
    ∃ Φ : C.obj ω₁ ≅ ωY, θM = ρψ.app ω₁ ≫ Ψb.map Φ.hom ≫ θb := by
  refine ⟨C.mapIso ρj.symm ≪≫ E.symm ≪≫ W.mapIso (asIso φ) ≪≫ ρw, ?_⟩
  have hΦ : (C.mapIso ρj.symm ≪≫ E.symm ≪≫ W.mapIso (asIso φ) ≪≫ ρw).hom =
      C.map ρj.inv ≫ E.inv ≫ W.map φ ≫ ρw.hom := rfl
  have n₁ := ρψ.naturality ρj.hom
  have n₂ := αs.naturality φ
  dsimp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
  rw [hΦ, ← cancel_epi (αr.app ωc ≫ ΨM.map ρj.hom), Category.assoc, ← h₁, h₂, Category.assoc,
    reassoc_of% n₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_map_assoc, ← reassoc_of% h₄,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% n₂, ← h₃]

/-- The diagram chase behind `NearbyCyclesModel.specialIdExchange_comp_pullbackExchange_square`:
both sides of the square are, up to the same isomorphism `e`, the pullback exchange `χ` of the
composite, by the two instances `ha`, `hb` of the composition law and the unit laws `hl`, `hr`. -/
lemma specialIdExchange_square_aux {D : Type*} [Category D]
    {A B B₁ B₂ U X₁ X₂ Y Z₁ Z₂ : D} {χ : A ⟶ B} {m₁ : B ⟶ B₁} {m₂ : B ⟶ B₂} {n : B₂ ⟶ B₁}
    {k₁ : A ⟶ X₁} {I₁ : X₁ ⟶ U} {Iinv : U ⟶ X₁} {e : A ⟶ U} [IsIso e] {Lr : X₁ ⟶ X₂}
    {aψ : X₂ ⟶ B₁} {αr : U ⟶ Y} {Iinv' : Y ⟶ X₂} {k₂ : A ⟶ Z₁} {LI : Z₁ ⟶ U}
    {LIinv : U ⟶ Z₁} {Lπ : Z₁ ⟶ Z₂} {aS : Z₂ ⟶ B₂} {LIπ : U ⟶ Z₂} {sψ : Y ⟶ B₁}
    (hn : m₂ ≫ n = m₁) (ha : χ ≫ m₁ = k₁ ≫ Lr ≫ aψ) (hb : χ ≫ m₂ = k₂ ≫ Lπ ≫ aS)
    (hl : k₁ ≫ I₁ = e) (hr : k₂ ≫ LI = e) (hI : I₁ ≫ Iinv = 𝟙 _) (hLI : LI ≫ LIinv = 𝟙 _)
    (hnat : αr ≫ Iinv' = Iinv ≫ Lr) (hLIπ : LIinv ≫ Lπ = LIπ) (hsψ : Iinv' ≫ aψ = sψ) :
    LIπ ≫ aS ≫ n = αr ≫ sψ := by
  have hk₁ : k₁ = e ≫ Iinv := by rw [← hl, Category.assoc, hI, Category.comp_id]
  have hk₂ : k₂ = e ≫ LIinv := by rw [← hr, Category.assoc, hLI, Category.comp_id]
  rw [← hLIπ, ← hsψ, ← cancel_epi e, Category.assoc, ← reassoc_of% hk₂, ← reassoc_of% hb, hn,
    ha, hk₁, reassoc_of% hnat, Category.assoc]

private lemma map_iso_hom_comp_inv {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B C : D} (e : A ≅ B) (f : A ⟶ C) :
    F.map e.hom ≫ F.map (e.inv ≫ f) = F.map f := by
  rw [← Functor.map_comp, Iso.hom_inv_id_assoc]

private lemma fullSubcategory_square_of_hom {D : Type*} [Category D] {P : ObjectProperty D}
    {A B C E F : P.FullSubcategory} {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ E}
    {d : A ⟶ F} {e : F ⟶ E} {a' : A.obj ⟶ B.obj} {b' : B.obj ⟶ C.obj}
    {c' : C.obj ⟶ E.obj} {d' : A.obj ⟶ F.obj} {e' : F.obj ⟶ E.obj}
    (ha : a.hom = a') (hb : b.hom = b') (hc : c.hom = c') (hd : d.hom = d')
    (he : e.hom = e') (h : a' ≫ b' ≫ c' = d' ≫ e') : a ≫ b ≫ c = d ≫ e := by
  apply ObjectProperty.hom_ext
  dsimp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [ha, hb, hc, hd, he]
  exact h

end Abstract

section AmbientShrink

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Y Z₁ Zc Zη S Sc : Scheme.{u}} {N : NearbyCyclesModel Y S} {M : NearbyCyclesModel Z₁ S}
  {P : NearbyCyclesModel Zc Sc} {P' : NearbyCyclesModel Zη Sc} {c : Y ⟶ Z₁} {j : Z₁ ⟶ Zc}
  {sb : Y ⟶ Zη} {π : Zη ⟶ Zc} {j' : S ⟶ Sc}

private lemma leftDerivedUpperStarCompOfEq_rfl :
    leftDerivedUpperStarCompOfEq Λ (rfl : c ≫ j = c ≫ j) =
      leftDerivedUpperStarComp Λ c j := rfl

private lemma specialIdExchange_map_comp (πc : P'.Hom P π (𝟙 Sc))
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology Zc) Ab.{u + 1}) (condensedRingObj Λ Zc))) :
    L((j')^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Sc).inv.app ((P.nearbyCycles Λ).obj C)) ≫
      L((j')^*⟦Λ⟧).map ((πc.pullbackExchange Λ).app C) =
      L((j')^*⟦Λ⟧).map (πc.specialIdExchange Λ C) := by
  rw [← Functor.map_comp]
  rfl

private lemma nearbyCycles_map_shrinkSquare_hom (hb : sb ≫ π = c ≫ j)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology Zc) Ab.{u + 1}) (condensedRingObj Λ Zc))) :
    (N.nearbyCycles Λ).map ((leftDerivedUpperStarCompOfEq Λ hb).hom.app C) ≫
      (N.nearbyCycles Λ).map ((leftDerivedUpperStarCompOfEq Λ hb).inv.app C ≫
        (leftDerivedUpperStarComp Λ c j).hom.app C) =
      (N.nearbyCycles Λ).map
        ((leftDerivedUpperStarCompOfEq Λ (rfl : c ≫ j = c ≫ j)).hom.app C) := by
  rw [leftDerivedUpperStarCompOfEq_rfl]
  exact map_iso_hom_comp_inv (N.nearbyCycles Λ)
    ((leftDerivedUpperStarCompOfEq Λ hb).app C) ((leftDerivedUpperStarComp Λ c j).hom.app C)

/-- **The exchange square of an open sub-model and of its shrunk model** (ambient): for morphisms
of models `ψ : N ⟶ M` over `c` and `𝟙`, `r : M ⟶ P` over `j, j'`, `s : N ⟶ P'` over `sb, j'`
and `π_c : P' ⟶ P` over `π` and `𝟙` with `s ≫ π_c = ψ ≫ r` and `sb ≫ π = c ≫ j`, the exchanges
through `L𝟙^* ≅ 𝟭` of `π_c` and `ψ` are compatible with the pullback exchanges of `s` and `r`:
both sides are the pullback exchange of the composite, by the composition law. -/
lemma specialIdExchange_comp_pullbackExchange_square (ψ : N.Hom M c (𝟙 S))
    (r : M.Hom P j j') (s : N.Hom P' sb j') (πc : P'.Hom P π (𝟙 Sc)) (hb : sb ≫ π = c ≫ j)
    (htot : s.total ≫ πc.total = ψ.total ≫ r.total)
    (hgen : s.generic ≫ πc.generic = ψ.generic ≫ r.generic)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology Zc) Ab.{u + 1}) (condensedRingObj Λ Zc))) :
    L((j')^*⟦Λ⟧).map (πc.specialIdExchange Λ C) ≫
      (s.pullbackExchange Λ).app (L((π)^*⟦Λ⟧).obj C) ≫
      (N.nearbyCycles Λ).map ((leftDerivedUpperStarCompOfEq Λ hb).inv.app C ≫
        (leftDerivedUpperStarComp Λ c j).hom.app C) =
    (r.pullbackExchange Λ).app C ≫ ψ.specialIdExchange Λ (L((j)^*⟦Λ⟧).obj C) := by
  have hj' : j' ≫ 𝟙 Sc = 𝟙 S ≫ j' := by rw [Category.comp_id, Category.id_comp]
  have ha := ψ.pullbackExchange_comp_app_of_eq Λ r (ψ.comp r) rfl rfl rfl rfl C
  have hb' := s.pullbackExchange_comp_app_of_eq Λ πc (ψ.comp r) hb hj' htot hgen C
  have hl := leftDerivedUpperStarComp_id_left_app Λ j' ((P.nearbyCycles Λ).obj C)
  have hr := leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId Λ hj'
    ((P.nearbyCycles Λ).obj C)
  have hn := (leftDerivedUpperStarId Λ S).inv.naturality ((r.pullbackExchange Λ).app C)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at hn
  have h₁ := specialIdExchange_map_comp Λ (j' := j') πc C
  have h₀ := nearbyCycles_map_shrinkSquare_hom Λ (N := N) hb C
  have h₃ : L((j')^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Sc).hom.app ((P.nearbyCycles Λ).obj C)) ≫
      L((j')^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Sc).inv.app ((P.nearbyCycles Λ).obj C)) =
      𝟙 _ :=
    ((leftDerivedUpperStarId Λ Sc).app ((P.nearbyCycles Λ).obj C)).hom_inv_id_map _
  exact specialIdExchange_square_aux h₀ ha hb' hl hr (Iso.hom_inv_id_app _ _) h₃ hn h₁ rfl

end AmbientShrink

section BoundedConstructibleShrink

variable {ℓ : ℕ} [Fact ℓ.Prime] {kY kX kS : Type u} [Field kY] [Field kX] [Field kS]
  [Fact (ringChar kY).Prime] [Fact (ringChar kY ≠ ℓ)] [Fact (ringChar kX).Prime]
  [Fact (ringChar kX ≠ ℓ)] [Fact (ringChar kS).Prime] [Fact (ringChar kS ≠ ℓ)]
  {Y Zη : Over (Spec (.of kY))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Zη.hom] [QuasiCompact Zη.hom] [IsSeparated Zη.hom]
  {Z₁ Zc : Over (Spec (.of kX))} [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Zc.hom] [QuasiCompact Zc.hom] [IsSeparated Zc.hom]
  {S Sc : Over (Spec (.of kS))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] [LocallyOfFiniteType Sc.hom] [QuasiCompact Sc.hom] [IsSeparated Sc.hom]
  {N : NearbyCyclesModel Y.left S.left} {M : NearbyCyclesModel Z₁.left S.left}
  {P : NearbyCyclesModel Zc.left Sc.left} {P' : NearbyCyclesModel Zη.left Sc.left}
  {c : Y.left ⟶ Z₁.left} {j : Z₁ ⟶ Zc} {sb : Y ⟶ Zη} {π : Zη.left ⟶ Zc.left} {j' : S ⟶ Sc}

variable (ℓ) in
/-- The comparison `sb^* π^* A ≅ c^* j^* A` of the pullbacks of bounded constructible complexes
along `sb ≫ π = c ≫ j`. -/
noncomputable def boundedConstructibleShrinkSquareIso (hb : sb.left ≫ π = c ≫ j.left)
    (A : Dᵇc(Zc.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ sb).obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := Zc) (Y := Zη) π).obj A) ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Z₁) (Y := Y) c).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj A) :=
  ObjectProperty.isoMk _
    ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hb).symm.app A.obj ≪≫
      (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) c j.left).app A.obj)

private lemma boundedConstructibleShrinkSquareIso_hom_hom (hb : sb.left ≫ π = c ≫ j.left)
    (A : Dᵇc(Zc.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleShrinkSquareIso ℓ hb A).hom.hom =
      (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hb).inv.app A.obj ≫
        (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) c j.left).hom.app A.obj :=
  rfl

private lemma boundedConstructibleNearbyCycles_map_hom''' {X X' : Scheme.{u}}
    {N : NearbyCyclesModel X X'}
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    {A B : Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B) :
    ((boundedConstructibleNearbyCycles hN).map f).hom =
      (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map f.hom :=
  rfl

omit [Fact (ringChar kS).Prime] [Fact (ringChar kS ≠ ℓ)]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] in
private lemma boundedConstructibleNearbyCycles_map_shrinkSquare_hom
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hb : sb.left ≫ π = c ≫ j.left) (A : Dᵇc(Zc.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleNearbyCycles hN).map
      (boundedConstructibleShrinkSquareIso ℓ hb A).hom).hom =
      (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hb).inv.app A.obj ≫
          (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) c j.left).hom.app A.obj) := by
  rw [boundedConstructibleNearbyCycles_map_hom''', boundedConstructibleShrinkSquareIso_hom_hom]

omit [Fact (ringChar kX).Prime] [Fact (ringChar kX ≠ ℓ)]
  [LocallyOfFiniteType Zc.hom] [QuasiCompact Zc.hom] [IsSeparated Zc.hom] in
private lemma boundedConstructiblePullbackExchange_app_upperStarOfMap_hom
    (s : N.Hom P' sb.left j'.left)
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hP' : P'.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A : Dᵇc(Zc.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((s.boundedConstructiblePullbackExchange ℓ hN hP').app
      ((boundedConstructibleUpperStarOfMap ℓ (X := Zc) (Y := Zη) π).obj A)).hom =
      (s.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app
        (L((π)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj) := by
  transport_exact s.boundedConstructiblePullbackExchange_app_hom ℓ hN hP'
    ((boundedConstructibleUpperStarOfMap ℓ (X := Zc) (Y := Zη) π).obj A)

private lemma boundedConstructibleSpecialIdExchange_square
    (ψ : N.Hom M c (𝟙 S.left)) (r : M.Hom P j.left j'.left)
    (s : N.Hom P' sb.left j'.left) (πc : P'.Hom P π (𝟙 Sc.left))
    (hb : sb.left ≫ π = c ≫ j.left)
    (htot : s.total ≫ πc.total = ψ.total ≫ r.total)
    (hgen : s.generic ≫ πc.generic = ψ.generic ≫ r.generic)
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hP : P.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hP' : P'.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (ρc : boundedConstructibleNearbyCycles hP ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := Zc) (Y := Zη) π ⋙
        boundedConstructibleNearbyCycles hP')
    (ρψ : boundedConstructibleNearbyCycles hM ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := Z₁) (Y := Y) c ⋙
        boundedConstructibleNearbyCycles hN)
    (hρc : ∀ A, (ρc.app A).hom = πc.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj)
    (hρψ : ∀ A, (ρψ.app A).hom = ψ.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj)
    (A : Dᵇc(Zc.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map (ρc.app A) ≫
        (s.boundedConstructiblePullbackExchange ℓ hN hP').app
          ((boundedConstructibleUpperStarOfMap ℓ (X := Zc) (Y := Zη) π).obj A) ≫
        (boundedConstructibleNearbyCycles hN).map
          (boundedConstructibleShrinkSquareIso ℓ hb A).hom =
      (r.boundedConstructiblePullbackExchange ℓ hM hP).app A ≫
        ρψ.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj A) := by
  refine fullSubcategory_square_of_hom
    ((boundedConstructibleUpperStar_map_hom _ _ j' (ρc.app A)).trans
      (congrArg (L((j'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map) (hρc A)))
    (boundedConstructiblePullbackExchange_app_upperStarOfMap_hom
      (Zc := Zc) (π := π) (sb := sb) (j' := j') s hN hP' A)
    (boundedConstructibleNearbyCycles_map_shrinkSquare_hom
      (c := c) (j := j) (sb := sb) (π := π) hN hb A)
    (r.boundedConstructiblePullbackExchange_app_hom ℓ (f := j) (f' := j') hM hP A)
    (hρψ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj A)) ?_
  transport_exact specialIdExchange_comp_pullbackExchange_square
    (Profinite.padicAlgClRingObj ℓ) ψ r s πc hb htot hgen A.obj

end BoundedConstructibleShrink

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfGenericBase

section Shrink

/-- The **shrunk model** of a trait model `M` over the generic base: the model `M` with the
inclusion `𝒳_Ω ⟶ 𝒳_η` of its geometric generic fibre into its generic fibre as identification, a
model of the generic fibre `𝒳_η` (`NearbyCyclesModel.traitGenericBase`). -/
noncomputable def shrink (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    NearbyCyclesModel (traitGenericBase q).left X'.left where
  total := M.total
  generic := M.generic
  j := M.j
  i := M.i
  ε := genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w

/-- **The shrunk model is a trait model over the generic base `(η, 𝒳_η, 𝟙)`**, with full generic
fibre. -/
theorem isTraitModelOfGenericBase_shrink (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    h.shrink.IsTraitModelOfGenericBase (traitGenericBase q) (𝟙 _) q g := by
  have hM := h.isTraitModelOver
  refine ⟨⟨hM.1, hM.2, hM.3, hM.4, hM.5⟩, inv (pullback.fst (traitGenericBase q).hom (𝟙 _)),
    inferInstance, ?_, ?_⟩
  · rw [IsIso.inv_comp_eq, ← Category.comp_id (pullback.snd (traitGenericBase q).hom _),
      ← pullback.condition]
    rfl
  · rw [IsIso.inv_hom_id, Category.comp_id]
    rfl

/-- The identity of `M` as a morphism of models `M♭ ⟶ M` from the shrunk model, over a map
`c : 𝒳_η ⟶ X₁` through which `ε` factors and the identity of the special fibre. -/
noncomputable def shrinkHom (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {c : (traitGenericBase q).left ⟶ X₁.left}
    (hc : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε) :
    h.shrink.Hom M c (𝟙 X'.left) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [shrink]
  comm_i := by simp [shrink]
  comm_ε := by simpa [shrink] using hc.symm

section BaseMap

variable {K : Type u} [Field K] [Algebra k' K] (x : K)

/-- **The slice base map of the shrunk model**: the map `c_M : X₂ ⟶ X₁` of the generic slice is
the map `c♭ : X₂ ⟶ 𝒳_η` of the generic slice of the shrunk model followed by `c`. -/
lemma genericSliceBaseMap_eq_shrink (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {c : (traitGenericBase q).left ⟶ X₁.left}
    (hc : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    h.genericSliceBaseMap x hb =
      h.isTraitModelOfGenericBase_shrink.genericSliceBaseMap x hb ≫ c := by
  have := h.epi_genericSliceModel_ε x hb
  refine (cancel_epi (genericSliceModel x hb).ε).1
    ((h.genericSliceModel_ε_comp_genericSliceBaseMap x hb).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ c)
    (h.isTraitModelOfGenericBase_shrink.genericSliceModel_ε_comp_genericSliceBaseMap x hb).symm)
  exact (congrArg (_ ≫ ·) hc.symm).trans (Category.assoc _ _ _).symm

/-- The projection `M'' ⟶ M♭` from the generic slice model to the shrunk model, as a morphism
from the generic slice model of `M` over the map of special fibres of the generic slice of `M`. -/
noncomputable def shrinkGenericSliceHom (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    (genericSliceModel x hb).Hom h.shrink
      (h.isTraitModelOfGenericBase_shrink.genericSliceBaseMap x hb)
      (sliceSpecialMap x h.isTraitModelOver hb) :=
  h.isTraitModelOfGenericBase_shrink.genericSliceHom x hb

end BaseMap

section Instances

variable {K : Type u} [Field K] [Algebra k' K] (x : K) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-! The generic slice of the shrunk model is that of the model. -/

instance [LocallyOfFiniteType (genericSliceBase x hb).hom] :
    LocallyOfFiniteType (genericSliceBase (M := h.shrink) x hb).hom :=
  ‹LocallyOfFiniteType (genericSliceBase x hb).hom›

instance [QuasiCompact (genericSliceBase x hb).hom] :
    QuasiCompact (genericSliceBase (M := h.shrink) x hb).hom :=
  ‹QuasiCompact (genericSliceBase x hb).hom›

instance [IsSeparated (genericSliceBase x hb).hom] :
    IsSeparated (genericSliceBase (M := h.shrink) x hb).hom :=
  ‹IsSeparated (genericSliceBase x hb).hom›

instance [LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom] :
    LocallyOfFiniteType (baseChangeSpecial (M := h.shrink) b (traitSlice x)).hom :=
  ‹LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom›

instance [QuasiCompact (baseChangeSpecial b (traitSlice x)).hom] :
    QuasiCompact (baseChangeSpecial (M := h.shrink) b (traitSlice x)).hom :=
  ‹QuasiCompact (baseChangeSpecial b (traitSlice x)).hom›

instance [IsSeparated (baseChangeSpecial b (traitSlice x)).hom] :
    IsSeparated (baseChangeSpecial (M := h.shrink) b (traitSlice x)).hom :=
  ‹IsSeparated (baseChangeSpecial b (traitSlice x)).hom›

end Instances

section Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]

/-- The **shrinking exchange** `Ψ_M ⟶ Ψ_{M♭} c^*` on bounded constructible complexes: the pullback
exchange of `NearbyCyclesModel.IsTraitModelOfGenericBase.shrinkHom`, through `L𝟙^* ≅ 𝟭` on the
special fibre. -/
noncomputable def shrinkExchange (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {c : (traitGenericBase q).left ⟶ X₁.left}
    (hc : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε) :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)) ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := traitGenericBase q) c ⋙
        boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ)) where
  app A := ObjectProperty.homMk
    ((h.shrinkHom hc).specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((h.shrinkHom hc).specialIdExchange_naturality (Profinite.padicAlgClRingObj ℓ) f.hom).symm

variable [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

/-- The slice exchange `α♭ : p^* Ψ_{M♭} ⟶ Ψ_{M''} c♭^*` of the shrunk model: the pullback exchange
of `NearbyCyclesModel.IsTraitModelOfGenericBase.shrinkGenericSliceHom`, on bounded constructible
complexes. -/
noncomputable def shrinkGenericSliceExchange :
    boundedConstructibleNearbyCycles
        (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := traitGenericBase q)
          (Y := genericSliceBase (M := M) (traitSliceCoord k') hb)
          (h.isTraitModelOfGenericBase_shrink.genericSliceBaseMap (traitSliceCoord k') hb) ⋙
        genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb :=
  liftExchange ((h.shrinkGenericSliceHom (traitSliceCoord k') hb).pullbackExchange
    (Profinite.padicAlgClRingObj ℓ)) _ _ _ _

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)] [LocallyOfFiniteType X₁.hom]
  [QuasiCompact X₁.hom] [IsSeparated X₁.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q] in
/-- The shrunk slice exchange is the slice exchange of the shrunk model. -/
lemma shrinkGenericSliceExchange_eq :
    shrinkGenericSliceExchange ℓ h hb =
      genericSliceExchange (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink hb :=
  rfl

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q] in
/-- **The slice exchange and shrinking** on bounded constructible complexes: the slice exchange
`α` of `M`, followed by `Ψ_{M''}` of `E : c_M^* ≅ c♭^* c^*`, is `p^*` of the shrinking exchange
followed by the slice exchange `α♭` of the shrunk model. -/
lemma genericSliceExchange_app_comp_map_shrink {c : (traitGenericBase q).left ⟶ X₁.left}
    (hc : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε)
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A ≫
      (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map
        (boundedConstructibleUpperStarOfMapCompIso ℓ (X := X₁) (Z := traitGenericBase q)
          (Y := genericSliceBase (M := M) (traitSliceCoord k') hb)
          (h.genericSliceBaseMap_eq_shrink (traitSliceCoord k') hc hb).symm A).hom =
    (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map ((h.shrinkExchange ℓ hc).app A) ≫
      (shrinkGenericSliceExchange ℓ h hb).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := traitGenericBase q) c).obj A) := by
  have key := liftExchange_comp_map_compIso_of_rebase (h.genericSliceHom (traitSliceCoord k') hb)
    (h.shrinkGenericSliceHom (traitSliceCoord k') hb) (h.shrinkHom hc)
    (h.genericSliceBaseMap_eq_shrink (traitSliceCoord k') hc hb).symm (Category.comp_id _)
    (Category.comp_id _) (h.preservesBoundedConstructible (ℓ := ℓ))
    (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ))
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
      h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ))
    (genericSliceExchange (traitSliceCoord k') ℓ h hb) rfl
    (shrinkGenericSliceExchange ℓ h hb) rfl (h.shrinkExchange ℓ hc)
    (fun _ ↦ by unfold shrinkExchange; exact ObjectProperty.homMk_hom _) A
  transport_exact key

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-- **The twist equation of the generic slice and shrinking the base**: let `M` be a trait model
over the generic base `(F, X₁, ι)`, `c : 𝒳_η ⟶ X₁` a map through which `ε` factors, and assume
that the dualizing map of `M` is that of its shrunk model `M♭` over `(η, 𝒳_η, 𝟙)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.shrink`) up to the shrinking exchange and an
identification `Φ : c^* ω_{X₁} ≅ ω_{𝒳_η}`: `θ_M = α ≫ Ψ_{M♭}(Φ) ≫ θ_{M♭}`. Then the twist
equation of `NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation` for `M♭`
implies it for `M`, with `u = E ≪≫ c♭^*(Φ) ≪≫ u♭` (`NearbyCyclesModel.exists_twist_of_rebase`). -/
theorem exists_iso_map_θ_eq_twist_of_shrink (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    {c : (traitGenericBase q).left ⟶ X₁.left}
    (hc : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε)
    (hθ : ∃ Φ : (boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := traitGenericBase q) c).obj
          (dualizingComplex ℓ X₁) ≅ dualizingComplex ℓ (traitGenericBase q),
      D.θ h = (h.shrinkExchange ℓ hc).app (dualizingComplex ℓ X₁) ≫
        (boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ))).map Φ.hom ≫
        D.θ h.isTraitModelOfGenericBase_shrink)
    (H : ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink
          hb).obj (dualizingComplex ℓ (traitGenericBase q)) ≅
        dualizingComplex ℓ (genericSliceBase (M := h.shrink) (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ
            (genericSliceBase (M := h.shrink) (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink
          hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial (M := h.shrink) b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial (M := h.shrink) b (traitSlice (traitSliceCoord k'))) 0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink hb).map
          (D.θ h.isTraitModelOfGenericBase_shrink) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink hb).app
            (dualizingComplex ℓ (traitGenericBase q)) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink
            hb).map u.hom ≫
          (genericSliceTwistIso ℓ h.isTraitModelOfGenericBase_shrink hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (M := h.shrink) (traitSliceCoord k')
            hb h.isTraitModelOfGenericBase_shrink.isTraitModelOver) ▷ _) :
    ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map u.hom ≫
          (genericSliceTwistIso ℓ h hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
            h.isTraitModelOver) ▷ _ := by
  obtain ⟨Φ, hΦ⟩ := hθ
  exact exists_twist_of_rebase_of_eq (D.θ h) (D.θ h.isTraitModelOfGenericBase_shrink)
    (h.shrinkExchange ℓ hc) Φ.hom hΦ
    (genericSliceExchange (traitSliceCoord k') ℓ h hb) (shrinkGenericSliceExchange ℓ h hb)
    (genericSliceExchange (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink hb)
    (shrinkGenericSliceExchange_eq ℓ h hb)
    (boundedConstructibleUpperStarOfMapCompIso ℓ (X := X₁) (Z := traitGenericBase q)
      (Y := genericSliceBase (M := M) (traitSliceCoord k') hb)
      (h.genericSliceBaseMap_eq_shrink (traitSliceCoord k') hc hb).symm _)
    (by transport_exact (genericSliceExchange_app_comp_map_shrink ℓ h hb hc
      (dualizingComplex ℓ X₁)))
    _ _ H

end Exchange

section OpenSubmodel

variable {Xc : Over (Spec (.of F))} {Xc' : Over (Spec (.of k'))}
  {Mc : NearbyCyclesModel Xc.left Xc'.left} {qc : Mc.total ⟶ trait k'}
  {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}

/-- For an open immersion of models `r : M ⟶ M_c` over `j, j'` and an open immersion
`sb : 𝒳_η ⟶ X_c,η` over `c ≫ j`, the morphism `r` as a morphism of models `M♭ ⟶ M_c'` from the
shrunk model of `M` to the re-based model of `M_c`, over `sb` and `j'`. -/
noncomputable def shrinkRebaseHom (hc : Mc.IsTraitModelOfGenericBase Xc ι qc gc)
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) {j : X₁ ⟶ Xc} {j' : X' ⟶ Xc'}
    (r : M.Hom Mc j.left j'.left) (hg : g = r.generic ≫ gc)
    {c : (traitGenericBase q).left ⟶ X₁.left}
    (hcε : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε)
    (sb : traitGenericBase q ⟶ genericBaseChange Xc ι)
    (hsb : sb.left ≫ pullback.fst Xc.hom ι = c ≫ j.left) :
    h.shrink.Hom hc.rebase sb.left j'.left where
  total := r.total
  generic := r.generic
  comm_j := r.comm_j
  comm_i := r.comm_i
  comm_ε := by
    dsimp only [rebase, shrink]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hsb, reassoc_of% hcε, r.comm_ε]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc r.generic, ← hg]
      have hw : sb.left ≫ pullback.snd Xc.hom ι = pullback.snd q (traitGenericSpec k') :=
        Over.w sb
      rw [hw, genericFibreInclusion_snd]

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
  [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom] [IsSeparated Xc.hom]
  [LocallyOfFiniteType Xc'.hom] [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom]

/-- **The dualizing map of an open sub-model of a proper model and shrinking**: let `M` be an open
sub-model of a proper trait model `M_c` over the generic base `(F, X_c, ι)` with proper `X_c`,
`X_c'` and full generic fibre, through open immersions `j`, `j'` and `r : M ⟶ M_c`, and let
`c : 𝒳_η ⟶ X₁` and the open immersion `sb : 𝒳_η ⟶ X_c,η` satisfy `sb ≫ π = c ≫ j`. Then
`θ_M = α ≫ Ψ_{M♭}(Φ) ≫ θ_{M♭}` for the shrinking exchange `α` and an identification
`Φ : c^* ω_{X₁} ≅ ω_{𝒳_η}`, as required by
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_shrink`.

`θ_M` is the restriction of `θ_{M_c}` (open restriction), which is `θ_{M_c'}` up to the
re-basing exchange and the comparison `φ` of the dualizing complexes
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_rebase_of_isProper`); `θ_{M_c'}`
restricts to `θ_{M♭}` along `NearbyCyclesModel.IsTraitModelOfGenericBase.shrinkRebaseHom`
(open restriction), and the exchanges form a commutative square
(`NearbyCyclesModel.specialIdExchange_comp_pullbackExchange_square`). -/
theorem exists_θ_eq_shrink_of_openSubmodel (D : NearbyDualizingDataOfGenericBase k' ℓ)
    [IsProper (CondensedRing.toPoint Xc).left] [IsProper (CondensedRing.toPoint Xc').left]
    (hc : Mc.IsTraitModelOfGenericBase Xc ι qc gc) [IsProper qc]
    (hgen : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ ι))
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) (j : X₁ ⟶ Xc) [IsOpenImmersion j.left]
    (j' : X' ⟶ Xc') [IsOpenImmersion j'.left] (r : M.Hom Mc j.left j'.left)
    [IsOpenImmersion r.total] (hr : IsPullback r.generic M.j Mc.j r.total)
    (hq : q = r.total ≫ qc) (hg : g = r.generic ≫ gc) {c : (traitGenericBase q).left ⟶ X₁.left}
    (hcε : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε)
    (sb : traitGenericBase q ⟶ genericBaseChange Xc ι) [IsOpenImmersion sb.left]
    (hsb : sb.left ≫ pullback.fst Xc.hom ι = c ≫ j.left) :
    ∃ Φ : (boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := traitGenericBase q) c).obj
          (dualizingComplex ℓ X₁) ≅ dualizingComplex ℓ (traitGenericBase q),
      D.θ h = (h.shrinkExchange ℓ hcε).app (dualizingComplex ℓ X₁) ≫
        (boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ))).map Φ.hom ≫
        D.θ h.isTraitModelOfGenericBase_shrink := by
  have := isProper_toPoint_genericBaseChange (X₁ := Xc) (ι := ι)
  have := isIso_dualizingComplexBaseChange_genericBaseChange Xc ι ℓ
  have : IsOpenImmersion (shrinkRebaseHom hc h r hg hcε sb hsb).total := ‹IsOpenImmersion r.total›
  have : IsIso (r.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    r.isIso_pullbackExchange_of_isOpenImmersion _ hr
  have : IsIso (r.boundedConstructiblePullbackExchange ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ))) :=
    r.isIso_boundedConstructiblePullbackExchange ℓ _ _
  have h₁ := D.map_θ_comp_dualizingComplexUpperStarIso hc h j j' r hr hq hg
  have h₂ := D.θ_eq_rebase_of_isProper hc hgen
  have h₃ := D.map_θ_comp_dualizingComplexUpperStarIso hc.isTraitModelOfGenericBase_rebase
    h.isTraitModelOfGenericBase_shrink sb j' (shrinkRebaseHom hc h r hg hcε sb hsb) hr hq hg
  have hρc : ∀ A, ((hc.rebaseExchange ℓ).app A).hom =
      hc.rebaseHom.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj :=
    fun _ ↦ by unfold rebaseExchange; exact ObjectProperty.homMk_hom _
  have hρψ : ∀ A, ((h.shrinkExchange ℓ hcε).app A).hom =
      (h.shrinkHom hcε).specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj :=
    fun _ ↦ by unfold shrinkExchange; exact ObjectProperty.homMk_hom _
  refine exists_θ_eq_of_openSubmodel_of_rebase
    (Ψc := boundedConstructibleNearbyCycles (hc.preservesBoundedConstructible (ℓ := ℓ)))
    (ΨM := boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)))
    (Ψη := boundedConstructibleNearbyCycles
      (hc.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ)))
    (Ψb := boundedConstructibleNearbyCycles
      (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ)))
    (J' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j')
    (J := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (W := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ sb)
    (D.θ hc) (D.θ h) (D.θ hc.isTraitModelOfGenericBase_rebase)
    (D.θ h.isTraitModelOfGenericBase_shrink) (dualizingComplexUpperStarIso ℓ j')
    (dualizingComplexUpperStarIso ℓ j) (dualizingComplexUpperStarIso ℓ sb)
    (dualizingComplexBaseChange ℓ
      (inv (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ
        (X := point F) (Y := point (FractionRing (PowerSeries k'))) ι)))
      (isPullback_genericBaseChange Xc ι))
    (r.boundedConstructiblePullbackExchange ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ)))
    ((shrinkRebaseHom hc h r hg hcε sb hsb).boundedConstructiblePullbackExchange ℓ
      (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ))
      (hc.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ)))
    (hc.rebaseExchange ℓ) (h.shrinkExchange ℓ hcε)
    (boundedConstructibleShrinkSquareIso ℓ hsb (dualizingComplex ℓ Xc)) ?_ ?_ ?_ ?_
  · exact h₁
  · exact h₂
  · exact h₃
  · transport_exact boundedConstructibleSpecialIdExchange_square
      (Y := traitGenericBase q) (Zη := genericBaseChange Xc ι) (Z₁ := X₁) (Zc := Xc)
      (S := X') (Sc := Xc') (h.shrinkHom hcε) r
      (shrinkRebaseHom hc h r hg hcε sb hsb) hc.rebaseHom hsb
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ))
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ))
      (hc.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ))
      (hc.rebaseExchange ℓ) (h.shrinkExchange ℓ hcε) hρc hρψ (dualizingComplex ℓ Xc)

end OpenSubmodel

section TraitFibre

/-- The identification `X' ≅ 𝒳 ×_S s` of the special fibre of a trait model with the special
fibre of its generic standard model. -/
noncomputable def toTraitStdSpecialFibre (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    X' ⟶ traitStdSpecialFibre q :=
  Over.homMk h.isTraitModelOver.isPullback_i.isoPullback.hom
    h.isTraitModelOver.isPullback_i.isoPullback_hom_snd

instance (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    IsOpenImmersion (h.toTraitStdSpecialFibre).left :=
  inferInstanceAs (IsOpenImmersion h.isTraitModelOver.isPullback_i.isoPullback.hom)

/-- The shrunk model of a trait model is isomorphic to the generic standard model
`NearbyCyclesModel.traitFibreModel q` of its total space: the identity on the total spaces, over
the identity of `𝒳_η` and the identification of the special fibres. -/
noncomputable def shrinkTraitFibreHom (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    h.shrink.Hom (traitFibreModel q) (Over.Hom.left (𝟙 (traitGenericBase q)))
      (h.toTraitStdSpecialFibre).left where
  total := 𝟙 _
  generic := h.isTraitModelOver.isPullback_j.isoPullback.hom
  comm_j := by
    rw [Category.comp_id]
    exact h.isTraitModelOver.isPullback_j.isoPullback_hom_fst
  comm_i := by
    rw [Category.comp_id]
    exact h.isTraitModelOver.isPullback_i.isoPullback_hom_fst
  comm_ε := by
    dsimp only [shrink]
    rw [Over.id_left, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, traitFibreModel_ε, pullback.lift_fst, genericFibreInclusion_fst]
      exact h.isTraitModelOver.isPullback_j.isoPullback_hom_fst
    · rw [Category.assoc, traitFibreModel_ε, pullback.lift_snd, genericFibreInclusion_snd,
        h.isTraitModelOver.isPullback_j.isoPullback_hom_snd_assoc]

lemma isPullback_shrinkTraitFibreHom (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    IsPullback (h.shrinkTraitFibreHom).generic h.shrink.j (traitFibreModel q).j
      (h.shrinkTraitFibreHom).total :=
  have : IsIso (h.shrinkTraitFibreHom).generic :=
    inferInstanceAs (IsIso h.isTraitModelOver.isPullback_j.isoPullback.hom)
  have : IsIso (h.shrinkTraitFibreHom).total := inferInstanceAs (IsIso (𝟙 M.total))
  IsPullback.of_horiz_isIso ⟨(h.shrinkTraitFibreHom).comm_j⟩

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [LocallyOfFiniteType (genericSliceBase (M := traitFibreModel q) (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (M := traitFibreModel q) (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (M := traitFibreModel q) (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType
    (baseChangeSpecial (M := traitFibreModel q) b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact
    (baseChangeSpecial (M := traitFibreModel q) b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated
    (baseChangeSpecial (M := traitFibreModel q) b (traitSlice (traitSliceCoord k'))).hom]

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] in
/-- **The twist equation for the shrunk model from the generic standard model**: the shrunk model
`M♭` of a trait model is isomorphic to the generic standard model of its total space
(`NearbyCyclesModel.IsTraitModelOfGenericBase.shrinkTraitFibreHom`), an open immersion of models
for the same coordinate, so the twist equation for `NearbyCyclesModel.traitFibreModel q` implies it
for `M♭`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel`). -/
theorem exists_iso_map_θ_eq_twist_shrink_of_traitFibreModel
    (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (H : ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel q) hb).obj
          (dualizingComplex ℓ (traitGenericBase q)) ≅
        dualizingComplex ℓ (genericSliceBase (M := traitFibreModel q) (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ
            (genericSliceBase (M := traitFibreModel q) (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel q) hb).obj
          (dualizingComplex ℓ (traitStdSpecialFibre q)) ≅
        dualizingComplex ℓ
            (baseChangeSpecial (M := traitFibreModel q) b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial (M := traitFibreModel q) b (traitSlice (traitSliceCoord k'))) 0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel q) hb).map
          (D.θ (isTraitModelOfGenericBase_traitFibreModel q)) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ
            (isTraitModelOfGenericBase_traitFibreModel q) hb).app
            (dualizingComplex ℓ (traitGenericBase q)) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ
            (isTraitModelOfGenericBase_traitFibreModel q) hb).map u.hom ≫
          (genericSliceTwistIso ℓ (isTraitModelOfGenericBase_traitFibreModel q) hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (M := traitFibreModel q)
            (traitSliceCoord k') hb
            (isTraitModelOfGenericBase_traitFibreModel q).isTraitModelOver) ▷ _) :
    ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink
          hb).obj (dualizingComplex ℓ (traitGenericBase q)) ≅
        dualizingComplex ℓ (genericSliceBase (M := h.shrink) (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ
            (genericSliceBase (M := h.shrink) (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink
          hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial (M := h.shrink) b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial (M := h.shrink) b (traitSlice (traitSliceCoord k'))) 0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink hb).map
          (D.θ h.isTraitModelOfGenericBase_shrink) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink hb).app
            (dualizingComplex ℓ (traitGenericBase q)) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_shrink
            hb).map u.hom ≫
          (genericSliceTwistIso ℓ h.isTraitModelOfGenericBase_shrink hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (M := h.shrink) (traitSliceCoord k')
            hb h.isTraitModelOfGenericBase_shrink.isTraitModelOver) ▷ _ := by
  have : IsOpenImmersion (Over.Hom.left (𝟙 (traitGenericBase q))) :=
    inferInstanceAs (IsOpenImmersion (𝟙 (traitGenericBase q).left))
  have : IsOpenImmersion (h.shrinkTraitFibreHom).total :=
    inferInstanceAs (IsOpenImmersion (𝟙 M.total))
  exact exists_iso_map_θ_eq_twist_of_openSubmodel ℓ h.isTraitModelOfGenericBase_shrink hb
    (isTraitModelOfGenericBase_traitFibreModel q) hb D DK (𝟙 (traitGenericBase q))
    h.toTraitStdSpecialFibre h.shrinkTraitFibreHom h.isPullback_shrinkTraitFibreHom
    (Category.id_comp q).symm h.isTraitModelOver.isPullback_j.isoPullback_hom_snd.symm
    (Category.id_comp b) H

/-- **The twist equation from the generic standard model**: for a trait model `M` over the generic
base whose dualizing map is that of its shrunk model up to the shrinking exchange along some
`c : 𝒳_η ⟶ X₁` and an identification of dualizing complexes (`hθ`), the twist equation for the
generic standard model `NearbyCyclesModel.traitFibreModel q` implies it for `M`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_shrink_of_traitFibreModel`
and `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_shrink`). -/
theorem exists_iso_map_θ_eq_twist_of_traitFibreModel
    [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
    (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (hθ : ∃ (c : (traitGenericBase q).left ⟶ X₁.left)
      (hc : genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ c = M.ε)
      (Φ : (boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := traitGenericBase q) c).obj
          (dualizingComplex ℓ X₁) ≅ dualizingComplex ℓ (traitGenericBase q)),
      D.θ h = (h.shrinkExchange ℓ hc).app (dualizingComplex ℓ X₁) ≫
        (boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_shrink.preservesBoundedConstructible (ℓ := ℓ))).map Φ.hom ≫
        D.θ h.isTraitModelOfGenericBase_shrink)
    (H : ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel q) hb).obj
          (dualizingComplex ℓ (traitGenericBase q)) ≅
        dualizingComplex ℓ (genericSliceBase (M := traitFibreModel q) (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ
            (genericSliceBase (M := traitFibreModel q) (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel q) hb).obj
          (dualizingComplex ℓ (traitStdSpecialFibre q)) ≅
        dualizingComplex ℓ
            (baseChangeSpecial (M := traitFibreModel q) b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial (M := traitFibreModel q) b (traitSlice (traitSliceCoord k'))) 0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel q) hb).map
          (D.θ (isTraitModelOfGenericBase_traitFibreModel q)) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ
            (isTraitModelOfGenericBase_traitFibreModel q) hb).app
            (dualizingComplex ℓ (traitGenericBase q)) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ
            (isTraitModelOfGenericBase_traitFibreModel q) hb).map u.hom ≫
          (genericSliceTwistIso ℓ (isTraitModelOfGenericBase_traitFibreModel q) hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (M := traitFibreModel q)
            (traitSliceCoord k') hb
            (isTraitModelOfGenericBase_traitFibreModel q).isTraitModelOver) ▷ _) :
    ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map u.hom ≫
          (genericSliceTwistIso ℓ h hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
            h.isTraitModelOver) ▷ _ := by
  obtain ⟨c, hc, Φ, hΦ⟩ := hθ
  exact exists_iso_map_θ_eq_twist_of_shrink ℓ h hb D DK hc ⟨Φ, hΦ⟩
    (exists_iso_map_θ_eq_twist_shrink_of_traitFibreModel ℓ h hb D DK H)
end TraitFibre

section RestrictOpen

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable {Xc : Over (Spec (.of F))} {Xc' : Over (Spec (.of k'))}
  {Mc : NearbyCyclesModel Xc.left Xc'.left} {qc : Mc.total ⟶ trait k'}
  {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom] [IsSeparated Xc.hom]
  [LocallyOfFiniteType Xc'.hom] [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom]
  [IsProper (CondensedRing.toPoint Xc).left] [IsProper (CondensedRing.toPoint Xc').left]
  (hMc : Mc.IsTraitModelOfGenericBase Xc ι qc gc) [IsProper qc]
  (V : Mc.total.Opens) [QuasiCompact V.ι]
  [LocallyOfFiniteType (Mc.restrictSpecialFibre V).hom]
  [QuasiCompact (Mc.restrictSpecialFibre V).hom] [IsSeparated (Mc.restrictSpecialFibre V).hom]
  {b : (Mc.restrictOpen V).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = V.ι ≫ qc)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [LocallyOfFiniteType
    (genericSliceBase (M := traitFibreModel
          (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (M := traitFibreModel
        (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (M := traitFibreModel
        (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial (M := traitFibreModel
        (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) b
    (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial (M := traitFibreModel
        (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) b
    (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial (M := traitFibreModel
        (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) b
    (traitSlice (traitSliceCoord k'))).hom]

/-- **The dualizing map of an open sub-model of a proper model is that of its shrunk model**: for
the restriction `M_c|_V` of a proper trait model with proper `X_c`, `X_c'` and full generic fibre,
`θ_{M_c|_V} = α ≫ Ψ(Φ) ≫ θ_{(M_c|_V)♭}` for the shrinking exchange along
`c : V_η ⟶ 𝒳_{c,η} ⟶ X_c ×_F η ⟶ X_c` and an identification `Φ` of dualizing complexes
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_θ_eq_shrink_of_openSubmodel`). -/
theorem exists_θ_eq_shrink_restrictOpen (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (hgen : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ ι)) :
    ∃ (c : (traitGenericBase (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)).left ⟶ Xc.left)
      (hc : genericFibreInclusion (Mc.restrictOpen V) (V.ι ≫ qc) ((Mc.j ⁻¹ᵁ V).ι ≫ gc)
        (hMc.restrictOpen V).isTraitModelOver.isPullback_j.w ≫ c = (Mc.restrictOpen V).ε)
      (Φ : (boundedConstructibleUpperStarOfMap ℓ (X := Xc)
          (Y := traitGenericBase (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) c).obj
          (dualizingComplex ℓ Xc) ≅
        dualizingComplex ℓ (traitGenericBase (T := (Mc.restrictOpen V).total) (V.ι ≫ qc))),
      D.θ (hMc.restrictOpen V) = ((hMc.restrictOpen V).shrinkExchange ℓ hc).app
          (dualizingComplex ℓ Xc) ≫
        (boundedConstructibleNearbyCycles ((hMc.restrictOpen V).isTraitModelOfGenericBase_shrink
          |>.preservesBoundedConstructible (ℓ := ℓ))).map Φ.hom ≫
        D.θ (hMc.restrictOpen V).isTraitModelOfGenericBase_shrink := by
  have hR := hMc.restrictOpen V
  let w := hMc.exists_openImmersion_genericFibre.choose
  have hw : IsOpenImmersion w := hMc.exists_openImmersion_genericFibre.choose_spec.1
  have hw₁ : w ≫ pullback.snd _ _ = pullback.snd _ _ :=
    hMc.exists_openImmersion_genericFibre.choose_spec.2.1
  have hw₂ : genericFibreInclusion Mc qc gc hMc.isTraitModelOver.isPullback_j.w ≫ w ≫
      pullback.fst _ _ = Mc.ε := hMc.exists_openImmersion_genericFibre.choose_spec.2.2
  let sb : traitGenericBase (T := (Mc.restrictOpen V).total) (V.ι ≫ qc) ⟶ genericBaseChange Xc ι :=
    Over.homMk (restrictGenericFibreMap V ≫ w) (by
      change (restrictGenericFibreMap V ≫ w) ≫ pullback.snd Xc.hom ι =
        pullback.snd (V.ι ≫ qc) (traitGenericSpec k')
      rw [Category.assoc, hw₁, restrictGenericFibreMap_snd])
  have : IsOpenImmersion sb.left :=
    inferInstanceAs (IsOpenImmersion (restrictGenericFibreMap V ≫ w))
  have hcε : genericFibreInclusion (Mc.restrictOpen V) (V.ι ≫ qc) ((Mc.j ⁻¹ᵁ V).ι ≫ gc)
      hR.isTraitModelOver.isPullback_j.w ≫ (restrictGenericFibreMap V ≫ w) ≫
        pullback.fst Xc.hom ι = (Mc.restrictOpen V).ε := by
    rw [restrictOpen_ε, ← hw₂, Category.assoc,
      genericFibreInclusion_restrictOpen_comp_assoc hMc.isTraitModelOver V]
  let j' : Mc.restrictSpecialFibre V ⟶ Xc' := Over.homMk (Mc.i ⁻¹ᵁ V).ι rfl
  have : IsOpenImmersion j'.left := inferInstanceAs (IsOpenImmersion (Mc.i ⁻¹ᵁ V).ι)
  have : IsOpenImmersion (Over.Hom.left (𝟙 Xc)) :=
    inferInstanceAs (IsOpenImmersion (𝟙 Xc.left))
  have : IsOpenImmersion (Mc.restrictOpenHom V).total := inferInstanceAs (IsOpenImmersion V.ι)
  have hθ := exists_θ_eq_shrink_of_openSubmodel ℓ D hMc hgen hR (𝟙 Xc) j'
    (Mc.restrictOpenHom V) (isPullback_morphismRestrict Mc.j V).flip rfl rfl hcε sb
    (by rw [Over.id_left, Category.comp_id]; rfl)
  exact ⟨_, hcε, hθ⟩

/-- **The twist equation for an open sub-model of a proper model, from its generic standard
model**: let `M_c` be a proper trait model over the generic base `(F, X_c, ι)` with proper `X_c`,
`X_c'` and full generic fibre, `V` an open of its total space with quasi-compact inclusion and
`b : V ⟶ 𝔸¹_S` a coordinate. Then the twist equation of
`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation` for the generic standard
model `NearbyCyclesModel.traitFibreModel (V ⟶ S)` (a model over `(η, V_η, 𝟙)` whose base is its
own generic fibre) implies it for the restriction `M_c|_V` over `(F, X_c, ι)`.

The shrunk model of `M_c|_V` is isomorphic to the generic standard model
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_shrink_of_traitFibreModel`),
and the dualizing map of `M_c|_V` is that of its shrunk model up to the shrinking exchange and an
identification of dualizing complexes
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_θ_eq_shrink_of_openSubmodel`, along
`V_η ⟶ 𝒳_{c,η} ⟶ X_c ×_F η`), so that
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_shrink` applies. -/
theorem exists_iso_map_θ_eq_twist_restrictOpen_of_traitFibreModel
    (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (hgen : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ ι))
    (H : ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel
                (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) hb).obj
          (dualizingComplex ℓ (traitGenericBase (T := (Mc.restrictOpen V).total) (V.ι ≫ qc))) ≅
        dualizingComplex ℓ
            (genericSliceBase (M := traitFibreModel
                  (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ
            (genericSliceBase (M := traitFibreModel
                  (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel
                (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) hb).obj
          (dualizingComplex ℓ (traitStdSpecialFibre (T := (Mc.restrictOpen V).total) (V.ι ≫ qc))) ≅
        dualizingComplex ℓ (baseChangeSpecial (M := traitFibreModel
              (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) b
            (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial (M := traitFibreModel
                (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) b
            (traitSlice (traitSliceCoord k'))) 0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (isTraitModelOfGenericBase_traitFibreModel
                (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) hb).map
          (D.θ (isTraitModelOfGenericBase_traitFibreModel
                (T := (Mc.restrictOpen V).total) (V.ι ≫ qc))) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ
            (isTraitModelOfGenericBase_traitFibreModel
                  (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) hb).app
            (dualizingComplex ℓ (traitGenericBase (T := (Mc.restrictOpen V).total) (V.ι ≫ qc))) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ
            (isTraitModelOfGenericBase_traitFibreModel
                  (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) hb).map u.hom ≫
          (genericSliceTwistIso ℓ (isTraitModelOfGenericBase_traitFibreModel
                (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)) hb
            _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (M := traitFibreModel
                (T := (Mc.restrictOpen V).total) (V.ι ≫ qc))
            (traitSliceCoord k') hb
            (isTraitModelOfGenericBase_traitFibreModel
                  (T := (Mc.restrictOpen V).total) (V.ι ≫ qc)).isTraitModelOver) ▷ _) :
    ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ (hMc.restrictOpen V) hb).obj
          (dualizingComplex ℓ Xc) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ (hMc.restrictOpen V) hb).obj
          (dualizingComplex ℓ (Mc.restrictSpecialFibre V)) ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ (hMc.restrictOpen V) hb).map
          (D.θ (hMc.restrictOpen V)) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ (hMc.restrictOpen V) hb).app
            (dualizingComplex ℓ Xc) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ (hMc.restrictOpen V) hb).map u.hom ≫
          (genericSliceTwistIso ℓ (hMc.restrictOpen V) hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
            (hMc.restrictOpen V).isTraitModelOver) ▷ _ := by
  exact exists_iso_map_θ_eq_twist_of_traitFibreModel ℓ (hMc.restrictOpen V) hb D DK
    (exists_θ_eq_shrink_restrictOpen ℓ hMc V D hgen) H

end RestrictOpen
end Shrink

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
