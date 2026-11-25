/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing

/-!
# Fourier inversion: the delta kernel on a trivial line bundle

`Rπ₀!(ℒ_ψ(h s) ⊗ π^* P) ≅ Ri₀!((i^* P)(-1)[-2])` for the trivial line bundle `π` with fibre
coordinate `s` and the zero locus `i` of a function `h` (blueprint `proposition-fourier-inversion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Base change of an Artin–Schreier kernel.** For a cartesian square
`g' : Y' ⟶ Y`, `π' : Y' ⟶ X'`, `π : Y ⟶ X`, `g : X' ⟶ X` of `k₀`-schemes and a function `φ` on
`Y`, pulling back `Rπ₀!(ℒ_ψ(φ) ⊗ π^* P)` along `g` is `Rπ'₀!(ℒ_ψ(g'^* φ) ⊗ π'^* g^* P)`,
naturally in the Weil complex `P` on `X`. -/
theorem WeilComplex.nonempty_iso_upperStar_tensorLisse_artinSchreierOf_comp_upperStar
    (ψ : AddChar k₀ (PadicAlgCl l)) {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (g : X' ⟶ X) (π' : Y' ⟶ X') (g' : Y' ⟶ Y) (sq : IsPullback g' π' π g)
    [π.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [π'.IsOver (Spec (CommRingCat.of k₀))] [g'.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated π'] [LocallyOfFiniteType π'] [QuasiCompact π']
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))] (φ : Γ(Y, ⊤)) :
    Nonempty (WeilComplex.upperStar π ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ φ) (isLisse_artinSchreierOf ψ φ) ⋙
        WeilComplex.derivedLowerShriek k₀ l π ⋙ WeilComplex.upperStar g ≅
      WeilComplex.upperStar g ⋙ WeilComplex.upperStar π' ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ (g'.appTop φ))
          (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l π') := by
  obtain ⟨BC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    π g π' g' sq
  obtain ⟨T⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar g'
    (artinSchreierOf ψ φ) (isLisse_artinSchreierOf ψ φ)
  obtain ⟨a⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) g' ψ φ
  obtain ⟨A⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso a
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ φ))
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨C₁⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) g' π
  obtain ⟨E⟩ := WeilComplex.nonempty_upperStar_iso_of_eq (k₀ := k₀) (l := l) sq.w
  obtain ⟨C₂⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) π' g
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ BC) ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight T (WeilComplex.derivedLowerShriek k₀ l π') ≪≫
      Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight A (WeilComplex.derivedLowerShriek k₀ l π'))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (C₁.symm ≪≫ E ≪≫ C₂) _ ≪≫ Functor.associator _ _ _⟩

/-- **The delta kernel on a trivial line bundle** (the relative form of blueprint
`proposition-fourier-inversion`). Let `h` be a function on a
`k₀`-scheme `X` (as a morphism `X ⟶ 𝔸¹`), with zero locus `i : Z ⟶ X` (the base change of
the zero section along `h`), let `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` be the trivial line bundle with
fibre coordinate `s`, and let `ψ` be nontrivial. Then

`Rπ₀!(ℒ_ψ(h s) ⊗ π^* P) ≅ Ri₀!((i^* P)(-1)[-2])`

naturally in the Weil complex `P` on `X`. Over the open set `h ≠ 0` the left side vanishes by
`AlgebraicGeometry.WeilComplex.isZero_derivedLowerShriek_tensorLisse_artinSchreierOf_upperStar`
and base change; over `Z` the kernel is `ℒ_{ψ,0} ≅ ℚ̄_ℓ` and the Thom isomorphism
`AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback`
applies; the recollement
`AlgebraicGeometry.WeilComplex.exists_isIso_app_of_isZero_upperStar` glues the two. -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (h : X ⟶ affineLine k₀)
    [h.IsOver (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    (i : Z ⟶ X) [i.IsOver (Spec (CommRingCat.of k₀))]
    (hi : IsPullback (Z ↘ Spec (CommRingCat.of k₀)) i
      (AffineSpace.zeroSection PUnit.{u + 1} (Spec (CommRingCat.of k₀))) h)
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.upperStar π ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ
          (π.appTop (h.appTop (AffineSpace.coord _ PUnit.unit)) *
            s.appTop (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l π ≅
      WeilComplex.upperStar i ⋙ WeilComplex.tateTwist k₀ l Z (-1) ⋙
        shiftFunctor _ (-2 : ℤ) ⋙ WeilComplex.derivedLowerShriek k₀ l i) := by
  set f := h.appTop (AffineSpace.coord _ PUnit.unit)
  set c := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  have : IsClosedImmersion i := MorphismProperty.of_isPullback hi inferInstance
  let U := X.basicOpen f
  have hrange : Set.range U.ι = (Set.range i)ᶜ := by
    rw [Scheme.Opens.range_ι, range_eq_compl_basicOpen_of_isPullback h i _ hi, compl_compl]
  obtain ⟨η, hη⟩ := WeilComplex.exists_isIso_app_of_isZero_upperStar (k₀ := k₀) (l := l)
    i U.ι hrange
  set F := WeilComplex.upperStar π ⋙
    WeilComplex.tensorLisse (artinSchreierOf ψ (π.appTop f * s.appTop c))
      (isLisse_artinSchreierOf ψ _) ⋙ WeilComplex.derivedLowerShriek k₀ l π
  -- over the open set `U = {h ≠ 0}` the kernel vanishes
  have hF (P : WeilComplex k₀ l X) : IsZero ((WeilComplex.upperStar U.ι).obj (F.obj P)) := by
    have : CompactSpace X :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)
        (f := X ↘ Spec (CommRingCat.of k₀))).1 inferInstance
    have : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k₀)) :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2
        (isCompact_iff_compactSpace.1 (isCompact_basicOpen X (U := ⊤)
          (by simpa using isCompact_univ) f))
    have : QuasiSeparated (U.toScheme ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (QuasiSeparated (U.ι ≫ X ↘ Spec (CommRingCat.of k₀)))
    have : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X ↘ Spec (CommRingCat.of k₀)))
    let πU := pullback.snd π U.ι
    let j' := pullback.fst π U.ι
    let : (pullback π U.ι).Over (Spec (CommRingCat.of k₀)) :=
      ⟨πU ≫ U.toScheme ↘ Spec (CommRingCat.of k₀)⟩
    have : πU.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : j'.IsOver (Spec (CommRingCat.of k₀)) :=
      ⟨by
        rw [← comp_over π (Spec (CommRingCat.of k₀)), pullback.condition_assoc]
        rfl⟩
    have : IsSeparated πU := MorphismProperty.pullback_snd _ _ inferInstance
    have : LocallyOfFiniteType πU := MorphismProperty.pullback_snd _ _ inferInstance
    have : QuasiCompact πU := MorphismProperty.pullback_snd _ _ inferInstance
    have : LocallyOfFiniteType (pullback π U.ι ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (LocallyOfFiniteType (πU ≫ U.toScheme ↘ Spec (CommRingCat.of k₀)))
    obtain ⟨e⟩ := WeilComplex.nonempty_iso_upperStar_tensorLisse_artinSchreierOf_comp_upperStar
      ψ π U.ι πU j' (IsPullback.of_hasPullback π U.ι) (π.appTop f * s.appTop c)
    have heq : j'.appTop (π.appTop f * s.appTop c) =
        πU.appTop (U.ι.appTop f) * (j' ≫ s).appTop c := by
      rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.condition,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply]
    rw [heq] at e
    exact (WeilComplex.isZero_derivedLowerShriek_tensorLisse_artinSchreierOf_upperStar ψ hψ πU
      (j' ≫ s) ((IsPullback.of_hasPullback π U.ι).flip.paste_vert hπ) (U.ι.appTop f)
      (X.isUnit_ι_appTop_basicOpen f) ((WeilComplex.upperStar U.ι).obj P)).of_iso (e.app P)
  have : ∀ P, IsIso ((Functor.whiskerLeft F η).app P) := fun P ↦ hη _ (hF P)
  have : IsIso (Functor.whiskerLeft F η) := NatIso.isIso_of_isIso_app _
  -- over the zero locus `Z` the kernel is constant
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsSeparated (Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i (Spec (CommRingCat.of k₀))]
    infer_instance
  let πZ := pullback.snd π i
  let i' := pullback.fst π i
  let : (pullback π i).Over (Spec (CommRingCat.of k₀)) :=
    ⟨πZ ≫ Z ↘ Spec (CommRingCat.of k₀)⟩
  have : πZ.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : i'.IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨by
      rw [← comp_over π (Spec (CommRingCat.of k₀)), pullback.condition_assoc, comp_over i]
      rfl⟩
  have : IsSeparated πZ := MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType πZ := MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact πZ := MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (pullback π i ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (πZ ≫ Z ↘ Spec (CommRingCat.of k₀)))
  obtain ⟨e⟩ := WeilComplex.nonempty_iso_upperStar_tensorLisse_artinSchreierOf_comp_upperStar
    ψ π i πZ i' (IsPullback.of_hasPullback π i) (π.appTop f * s.appTop c)
  have hif : i.appTop f = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← hi.w, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.zeroSection_appTop_coord, map_zero]
  have heq : i'.appTop (π.appTop f * s.appTop c) = 0 := by
    rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.condition,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hif, map_zero, zero_mul]
  rw [heq] at e
  have hπZ := (IsPullback.of_hasPullback π i).flip.paste_vert hπ
  rw [comp_over] at hπZ
  obtain ⟨a₀⟩ := nonempty_iso_artinSchreierOf_zero (k₀ := k₀) (l := l) (X := pullback π i) ψ
  obtain ⟨t₀⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso a₀ (isLisse_artinSchreierOf ψ _)
    (WeilSheaf.isLisse_adicConstant k₀ l _)
  obtain ⟨t₁⟩ := WeilComplex.nonempty_iso_tensorLisse_adicConstant (k₀ := k₀) (l := l)
    (X := pullback π i)
  obtain ⟨Th⟩ := WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback
    (k₀ := k₀) (l := l) πZ (i' ≫ s) hπZ
  obtain ⟨Pr⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_derivedLowerStar
    (k₀ := k₀) (l := l) i
  let M : WeilComplex.upperStar πZ ⋙ WeilComplex.tensorLisse (artinSchreierOf ψ 0)
      (isLisse_artinSchreierOf ψ _) ⋙ WeilComplex.derivedLowerShriek k₀ l πZ ≅
      WeilComplex.tateTwist k₀ l Z (-1) ⋙ shiftFunctor _ (-2 : ℤ) :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (t₀ ≪≫ t₁) _ ≪≫ Functor.leftUnitor _) ≪≫
      Th
  exact ⟨asIso (Functor.whiskerLeft F η) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (e ≪≫ Functor.isoWhiskerLeft _ M) _ ≪≫
    Functor.isoWhiskerLeft _ Pr.symm ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _)⟩

end AlgebraicGeometry
