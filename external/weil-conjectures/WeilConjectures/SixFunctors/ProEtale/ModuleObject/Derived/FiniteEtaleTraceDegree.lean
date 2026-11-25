/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceCover

/-!
# Split units along finite étale covers of invertible geometric degree

Let `v : W ⟶ U` be finite étale, all of whose geometric fibres have `d` points. Over a weakly
étale `U`-scheme `T` on which `T ×_U W` splits as a disjoint union of copies of `T` indexed by
`J`, the geometric fibre of `v` over any geometric point of `T` is in bijection with `J`; hence
every such splitting over a nonempty `T` has `d` sheets, and `v` is pro-étale locally split into
`d` sheets. For finite coefficients `C(-, T)` in which `d` is invertible, the unit of
`Lv^* ⊣ Rv_*` is then a split monomorphism.

## Main results

- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.nat_card_eq_of_isColimit`: if `p : P ⟶ T` has
  sections `s j` exhibiting `P` as a coproduct of copies of `T`, the geometric fibre of `p` over
  any geometric point of `T` is in bijection with the index type.
- `AlgebraicGeometry.ProEtale.TraceSplitting.card_eq_of_geometricFiber_card`: a splitting of a
  morphism of geometric degree `d` over a nonempty base has `d` sheets.
- `AlgebraicGeometry.ProEtale.CondensedRing.
  isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_geometricFiber_card`:
  for finite coefficients and a finite étale `v` of geometric degree `d` invertible in the
  coefficients, the unit of the derived adjunction `Lv^* ⊣ Rv_*` is a split monomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.Hom.GeometricFiber

/-- **Geometric fibres of a split cover**: if the sections `s j : T ⟶ P` of `p : P ⟶ T` exhibit
`P` as a coproduct of copies of `T`, then the geometric points of `P` over a geometric point `x`
of `T` are exactly the `x ≫ s j`, so their number is the number of sheets. -/
theorem nat_card_eq_of_isColimit {T P : Scheme.{u}} {J : Type u} (p : P ⟶ T) (s : J → (T ⟶ P))
    (hs : ∀ j, s j ≫ p = 𝟙 T) (hc : IsColimit (Cofan.mk P s)) {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ T) :
    Nat.card (p.GeometricFiber x) = Nat.card J := by
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor fun _ : J ↦ T))
  have he (j : J) : s j ≫ e.hom = Sigma.ι (fun _ : J ↦ T) j :=
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨j⟩
  refine (Nat.card_eq_of_bijective (fun j ↦ ⟨x ≫ s j, by rw [Category.assoc, hs, Category.comp_id]⟩)
    ⟨fun i j hij ↦ ?_, fun y ↦ ?_⟩).symm
  · have h := congrArg (fun f ↦ (f ≫ e.hom) (default : Spec (.of Ω))) (congrArg Subtype.val hij)
    simp only [Category.assoc, he, Scheme.Hom.comp_apply] at h
    exact congrArg Sigma.fst ((sigmaι_eq_iff _ i j _ _).mp h)
  · obtain ⟨⟨j, z⟩, hz⟩ := (sigmaMk fun _ : J ↦ T).surjective ((y.1 ≫ e.hom) default)
    rw [sigmaMk_mk] at hz
    have hr : Set.range (y.1 ≫ e.hom).base ⊆ Set.range (Sigma.ι (fun _ : J ↦ T) j).base := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q default]
      exact ⟨z, hz⟩
    let w := IsOpenImmersion.lift (Sigma.ι (fun _ : J ↦ T) j) (y.1 ≫ e.hom) hr
    have hw : w ≫ Sigma.ι (fun _ : J ↦ T) j = y.1 ≫ e.hom := IsOpenImmersion.lift_fac _ _ _
    have hy : w ≫ s j = y.1 := by
      rw [← cancel_mono e.hom, Category.assoc, he, hw]
    have hwx : w = x := by
      rw [← y.2, ← hy, Category.assoc, hs, Category.comp_id]
    exact ⟨j, Subtype.ext (by rw [← hy, hwx])⟩

end AlgebraicGeometry.Scheme.Hom.GeometricFiber

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **Splittings of a cover of geometric degree `d` have `d` sheets**: if every geometric fibre of
`g` over a separably closed field has `d` points, then every splitting of `T ×_X Y` over a
nonempty weakly étale `X`-scheme `T` has `d` sheets. -/
theorem TraceSplitting.card_eq_of_geometricFiber_card {X Y : Scheme.{u}} {g : Y ⟶ X}
    [WeaklyEtale g] {d : ℕ}
    (hcard : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (g.GeometricFiber s) = d)
    {T : X.ProEt} (D : TraceSplitting g T) (hT : Nonempty T.left) :
    Fintype.card D.J = d := by
  obtain ⟨t⟩ := hT
  let x : Spec (.of (AlgebraicClosure (T.left.residueField t))) ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t)
      (AlgebraicClosure (T.left.residueField t)))) ≫ T.left.fromSpecResidueField t
  have hs (j : D.J) : (D.s j).left ≫ pullback.fst T.hom g = 𝟙 T.left := by
    exact congrArg (fun f ↦ f.left) (D.s_proj j)
  rw [← Nat.card_eq_fintype_card, ← hcard _ (x ≫ T.hom), ← Nat.card_congr
    (Hom.GeometricFiber.baseChangeEquiv (IsPullback.of_hasPullback T.hom g).flip x)]
  exact (Hom.GeometricFiber.nat_card_eq_of_isColimit _ _ hs D.isColimit x).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- **Split derived units along a finite étale cover of invertible degree**, for finite
coefficients `C(-, T)`: let `v : W ⟶ U` be finite étale, all of whose geometric fibres over
separably closed fields have `d` points, with `d` invertible in `T`. Then the unit of the derived
adjunction `Lv^* ⊣ Rv_*` is a split monomorphism at every complex. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_geometricFiber_card
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
    [Finite T] {U W : Scheme.{u}} (v : W ⟶ U) [IsFinite v] [Etale v] {d : ℕ}
    (hd : IsUnit (d : T))
    (hcard : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Nat.card (v.GeometricFiber s) = d)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) U))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T)
      v).unit.app G) := by
  let Λ := Profinite.continuousMapRingObj.{u} T
  have hg : IsLocallySplit v d := isLocallySplit_of_finite_of_etale v
    fun _ D hT ↦ D.card_eq_of_geometricFiber_card hcard hT
  have : IsIso ((upperStarLowerStarAdjunction Λ v).unit ≫ splitTraceModule Λ hg) := by
    have (M : _) : IsIso (((upperStarLowerStarAdjunction Λ v).unit ≫
        splitTraceModule Λ hg).app M) := by
      let _ := modLinear Λ (Profinite.continuousMapConstRingHom.{u} T) U
      rw [unit_comp_splitTraceModule, NatTrans.app_nsmul, NatTrans.id_app]
      obtain ⟨c, hc⟩ := hd
      rw [← Nat.cast_smul_eq_nsmul T, ← hc]
      refine ⟨(↑c⁻¹ : T) • 𝟙 M, ?_, ?_⟩
      · simp only [Functor.id_obj, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
          smul_smul, Units.inv_mul, one_smul]
      · simp only [Functor.id_obj, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
          smul_smul, Units.mul_inv, one_smul]
    exact NatIso.isIso_of_isIso_app _
  exact isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_trace Λ v
    (splitTraceModule Λ hg) G

end AlgebraicGeometry.ProEtale.CondensedRing
