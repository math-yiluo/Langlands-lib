/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.WeilSheaf.DirectImageStalk
public import WeilConjectures.WeilSheaf.LowerStarComp

/-!
# The direct image along an open immersion commutes with restriction to an open

Consider a cartesian square of `k₀`-schemes

```
U' --j'--> X'
|          |
ι'         ι
v          v
U  --j-->  C
```

with `j` a quasi-compact open immersion and `ι` a quasi-compact open immersion. For a Weil sheaf
`F` on `U` and a closed point `y` of `X'`, the stalk of `j_* F` at `ι y` is the stalk of
`j'_* (ι'^* F)` at `y`, compatibly with the local Frobenius
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage_of_isPullback`). This is Step 0
of the proof of `proposition-weights-j-boundary-points--1`: the formation of `j_*` commutes with
restriction to an open.

The proof goes through the Weil sheaf `j_* ι'_* ι'^* F = ι_* j'_* ι'^* F`. The image under
`ι^* j_*` of the unit `F ⟶ ι'_* ι'^* F` is an isomorphism: by the weakly étale base change
isomorphism `ῑ^* j̄_* ≅ j̄'_* ῑ'^*` (`AlgebraicGeometry.ProEtale.adicBaseChangeMap`) of the
geometric fibres, it corresponds to `j̄'_*` of `ῑ'^*` of the unit, which is an isomorphism by
the triangle identity, the counit of `ῑ'^* ⊣ ῑ'_*` being an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isPullback_geometricFiberMap_of_isPullback`: base change to
  `k̄` preserves cartesian squares.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_upperStar`: the stalk of a pullback at a
  closed point whose image has the same degree.
- `AlgebraicGeometry.WeilSheaf.isIso_upperStar_map_lowerStar_map_unit`: `ι^* j_*` of the unit
  `F ⟶ ι'_* ι'^* F` is an isomorphism.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage_of_isPullback`: the stalks of
  `j_* F` along `X'` are those of `j'_* (ι'^* F)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {k : Type u} [Field k] {P X Y Z : Scheme.{u}} {fP : P ⟶ Spec (.of k)}
  {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {fZ : Z ⟶ Spec (.of k)}

/-- Base change to the algebraic closure preserves cartesian squares of schemes over `k`. -/
theorem isPullback_geometricFiberMap_of_isPullback {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hfst : fst ≫ fX = fP) (hsnd : snd ≫ fY = fP)
    (hf : f ≫ fZ = fX) (hg : g ≫ fZ = fY) :
    IsPullback (geometricFiberMap fst hfst) (geometricFiberMap snd hsnd)
      (geometricFiberMap f hf) (geometricFiberMap g hg) := by
  -- paste with the cartesian square of `f` and its base change, then with the given square
  refine IsPullback.of_right (h₁₂ := fX.geometricFiberProj) (h₂₂ := fZ.geometricFiberProj)
    (v₁₃ := f) ?_ ?_ (isPullback_geometricFiberMap f hf).flip
  · rw [geometricFiberMap_comp_geometricFiberProj, geometricFiberMap_comp_geometricFiberProj]
    exact (isPullback_geometricFiberMap snd hsnd).flip.paste_horiz h
  · rw [← geometricFiberMap_comp, ← geometricFiberMap_comp]
    congr 1
    exact h.w

end Scheme.Hom

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The stalk of a pullback.** For a morphism `φ : X ⟶ Y` of `k₀`-schemes, a Weil sheaf `G` on
`Y` and a closed point `z` of `X` whose image `x = φ z` has the same degree over `k₀` (e.g. `φ`
an open immersion), the stalk of `φ^* G` at `z` is the stalk of `G` at `x`, compatibly with the
local Frobenius. -/
theorem nonempty_equiv_stalk_upperStar {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l Y) (z : X.finitePoints) (x : Y.finitePoints) (hzx : φ.base z.1 = x.1)
    (hdeg : (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 =
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) :
    Nonempty ((((upperStar φ).obj G).stalk z).Equiv (G.stalk x)) := by
  have hφ := comp_over φ (Spec (CommRingCat.of k₀))
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) z
  have ht' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have ht'' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).asIso.hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := hdeg ▸ ht'
  -- the stalk of `φ^* G` at `z` is the stalk of `G` at `s ≫ φ̄`
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      G.obj.carrier.X ⟶ ((upperStar φ).obj G).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      G.obj.carrier.X)))
  obtain ⟨e₂⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (upperStar φ).obj G)
    (θ := 𝟙 _) (upperStar_frobeniusStr_compatible (φ := φ) G) s _ ht ht'
  -- the geometric points over `x`: the chosen one and `s ≫ φ̄`
  have hx₁ := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (Y ↘ Spec (CommRingCat.of k₀)) x
  have hss' : ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hx₁, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc, Scheme.Hom.comp_base, TopCat.comp_app,
      Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base, hzx]
  obtain ⟨e₃⟩ := G.nonempty_equiv_stalkAt _ _ hss' (hx₁ ▸ x.2) _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (Y ↘ Spec (CommRingCat.of k₀)) x) ht''
  obtain ⟨e₄⟩ := G.nonempty_equiv_stalkAt_of_eq _ hdeg.symm ht'' ht'
  exact ⟨((e₃.trans e₄).trans e₂).symm⟩

omit [Fact (ringChar k₀ ≠ l)] in
/-- Pushforwards along equal morphisms agree. -/
private lemma nonempty_iso_lowerStar_of_eq {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {φ ψ : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))]
    [ψ.IsOver (Spec (CommRingCat.of k₀))] (h : φ = ψ) (F : ProEtaleWeilSheaf k₀ l X) :
    Nonempty ((ProEtaleWeilSheaf.lowerStar k₀ l φ).obj F ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l ψ).obj F) := by
  subst h
  exact ⟨Iso.refl _⟩

section Restriction

variable {C X' U U' : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
  [U'.Over (Spec (CommRingCat.of k₀))] {j : U ⟶ C} {ι : X' ⟶ C} {j' : U' ⟶ X'} {ι' : U' ⟶ U}
  [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  [IsOpenImmersion ι] [QuasiCompact ι] [ι.IsOver (Spec (CommRingCat.of k₀))]
  [IsOpenImmersion j'] [QuasiCompact j'] [j'.IsOver (Spec (CommRingCat.of k₀))]
  [IsOpenImmersion ι'] [QuasiCompact ι'] [ι'.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]

omit [QuasiCompact ι] [IsOpenImmersion j'] [QuasiCompact j']
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))] in
/-- For a cartesian square `j' ≫ ι = ι' ≫ j` of quasi-compact open immersions, the image under
`ι^* j_*` of the unit `F ⟶ ι'_* ι'^* F` is an isomorphism. On the geometric fibres, weakly étale
base change `ῑ^* j̄_* ≅ j̄'_* ῑ'^*` (`AlgebraicGeometry.ProEtale.adicBaseChangeMap`) turns it into
`j̄'_*` of `ῑ'^*` of the unit, an isomorphism by the triangle identity since the counit of
`ῑ'^* ⊣ ῑ'_*` is one. -/
theorem isIso_upperStar_map_lowerStar_map_unit (h : IsPullback j' ι' ι j)
    (F : WeilSheaf k₀ l U) :
    IsIso ((upperStar ι).map ((lowerStar j).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) ι').unit.app F))) := by
  have hsq := Scheme.Hom.isPullback_geometricFiberMap_of_isPullback h
    (comp_over j' (Spec (CommRingCat.of k₀))) (comp_over ι' (Spec (CommRingCat.of k₀)))
    (comp_over ι (Spec (CommRingCat.of k₀))) (comp_over j (Spec (CommRingCat.of k₀)))
  set adj := ProEtale.adicUpperStarLowerStarAdjunction l
    (Scheme.Hom.geometricFiberMap ι' (comp_over ι' (Spec (CommRingCat.of k₀))))
  set M := F.obj.carrier
  have hη : IsIso ((Scheme.Hom.geometricFiberMap ι' (comp_over ι' _))^*ᵃ[l].map
      (adj.unit.app M)) := by
    have h₁ := adj.left_triangle_components M
    have : IsIso ((Scheme.Hom.geometricFiberMap ι' (comp_over ι' _))^*ᵃ[l].map
        (adj.unit.app M) ≫ adj.counit.app _) := by
      rw [h₁]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have hβ := (ProEtale.adicBaseChangeMap l hsq.toCommSq).naturality (adj.unit.app M)
  have hB : IsIso (ProEtale.adicBaseChangeMap l hsq.toCommSq) :=
    ProEtale.isIso_adicBaseChangeMap_of_isPullback l hsq
  have hu : IsIso ((Scheme.Hom.geometricFiberMap ι (comp_over ι _))^*ᵃ[l].map
      ((Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l].map (adj.unit.app M))) := by
    have : IsIso (((Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l] ⋙
        (Scheme.Hom.geometricFiberMap ι (comp_over ι _))^*ᵃ[l]).map (adj.unit.app M) ≫
          (ProEtale.adicBaseChangeMap l hsq.toCommSq).app _) := by
      rw [hβ, Functor.comp_map]
      have h₂ := Functor.map_isIso
        (Scheme.Hom.geometricFiberMap j' (comp_over j' _))_*ᵃ[l]
        ((Scheme.Hom.geometricFiberMap ι' (comp_over ι' _))^*ᵃ[l].map (adj.unit.app M))
      exact IsIso.comp_isIso
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
      ((ProEtale.adicBaseChangeMap l hsq.toCommSq).app _) _ this
  have : IsIso ((upperStar ι).map ((lowerStar j).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) ι').unit.app F))).hom.hom.f := hu
  exact isIso_of_isIso_hom_hom_f _

omit [QuasiCompact ι] [IsOpenImmersion j'] [QuasiCompact j']
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))] in
/-- The isomorphism `ι^* j_* F ≅ ι^* j_* ι'_* ι'^* F` induced by the unit. -/
private lemma nonempty_iso_upperStar_lowerStar_unit (h : IsPullback j' ι' ι j)
    (F : WeilSheaf k₀ l U) :
    Nonempty ((upperStar ι).obj ((lowerStar j).obj F) ≅
      (upperStar ι).obj ((lowerStar j).obj ((lowerStar ι').obj ((upperStar ι').obj F)))) := by
  have := isIso_upperStar_map_lowerStar_map_unit h F
  exact ⟨(upperStar ι).mapIso ((lowerStar j).mapIso (eqToIso (Functor.id_obj F).symm)) ≪≫
    asIso ((upperStar ι).map ((lowerStar j).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) ι').unit.app F))) ≪≫
    (upperStar ι).mapIso ((lowerStar j).mapIso (eqToIso (Functor.comp_obj _ _ F)))⟩

/-- The isomorphism `j_* ι'_* G ≅ ι_* j'_* G` of pushforwards along the two sides of a
commutative square. -/
private lemma nonempty_iso_lowerStar_lowerStar (h : j' ≫ ι = ι' ≫ j) (G : WeilSheaf k₀ l U') :
    Nonempty ((lowerStar j).obj ((lowerStar ι').obj G) ≅
      (lowerStar ι).obj ((lowerStar j').obj G)) := by
  obtain ⟨c⟩ := nonempty_iso_lowerStar_of_eq (k₀ := k₀) (l := l) h.symm G.obj
  have e₁ : ((lowerStar j).obj ((lowerStar ι').obj G)).obj =
      (ProEtaleWeilSheaf.lowerStar k₀ l ι' ⋙ ProEtaleWeilSheaf.lowerStar k₀ l j).obj G.obj := by
    simp only [lowerStar, ObjectProperty.liftFullSubcategory_obj_obj, Functor.comp_obj]
  have e₂ : (ProEtaleWeilSheaf.lowerStar k₀ l j' ⋙ ProEtaleWeilSheaf.lowerStar k₀ l ι).obj G.obj =
      ((lowerStar ι).obj ((lowerStar j').obj G)).obj := by
    simp only [lowerStar, ObjectProperty.liftFullSubcategory_obj_obj, Functor.comp_obj]
  exact ⟨ObjectProperty.isoMk _ (eqToIso e₁ ≪≫
    (ProEtaleWeilSheaf.lowerStarCompIso k₀ l ι' j).app G.obj ≪≫ c ≪≫
      ((ProEtaleWeilSheaf.lowerStarCompIso k₀ l j' ι).app G.obj).symm ≪≫ eqToIso e₂)⟩

/-- **The direct image commutes with restriction to an open** (Step 0 of the proof of
`proposition-weights-j-boundary-points--1`). For a cartesian square `j' ≫ ι = ι' ≫ j` of
quasi-compact open immersions of `k₀`-schemes, a Weil sheaf `F` on `U` and a closed point `y` of
`X'` over the closed point `x = ι y` of `C`, the stalk of `j_* F` at `x` is the stalk of
`j'_* (ι'^* F)` at `y`, compatibly with the local Frobenius.

Both are stalks of `ι^* j_* F`, resp. of `ι_* j'_* ι'^* F = j_* ι'_* ι'^* F`, and `ι^* j_*`
of the unit `F ⟶ ι'_* ι'^* F` is an isomorphism
(`AlgebraicGeometry.WeilSheaf.isIso_upperStar_map_lowerStar_map_unit`). -/
theorem nonempty_equiv_stalk_directImage_of_isPullback (h : IsPullback j' ι' ι j)
    (F : WeilSheaf k₀ l U) (y : X'.finitePoints) (x : C.finitePoints) (hyx : ι.base y.1 = x.1) :
    Nonempty ((((directImage j).obj F).stalk x).Equiv
      (((directImage j').obj ((upperStar ι').obj F)).stalk y)) := by
  have hdeg : (X' ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 =
      (C ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 := by
    rw [← hyx, ← Scheme.Hom.degreeOver_comp_of_isIso ι (C ↘ Spec (CommRingCat.of k₀)) y.1,
      comp_over ι]
  obtain ⟨e₁⟩ := nonempty_equiv_stalk_upperStar ι ((lowerStar j).obj F) y x hyx hdeg
  obtain ⟨i₂⟩ := nonempty_iso_upperStar_lowerStar_unit h F
  obtain ⟨e₃⟩ := nonempty_equiv_stalk_upperStar ι
    ((lowerStar j).obj ((lowerStar ι').obj ((upperStar ι').obj F))) y x hyx hdeg
  obtain ⟨i₄⟩ := nonempty_iso_lowerStar_lowerStar h.w ((upperStar ι').obj F)
  obtain ⟨e₅⟩ := nonempty_equiv_stalk_directImage ι ((lowerStar j').obj ((upperStar ι').obj F))
    y x hyx
  obtain ⟨e₂⟩ := nonempty_equiv_stalk_of_iso i₂ y
  obtain ⟨e₄⟩ := nonempty_equiv_stalk_of_iso i₄ x
  exact ⟨(((e₁.symm.trans e₂).trans e₃).trans e₄).trans e₅⟩

end Restriction

end AlgebraicGeometry.WeilSheaf
