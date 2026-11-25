/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.Profinite.Limits
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstantHom

/-!

# `LocallyConstant (-, ℤ)` sends pullbacks of profinite sets to pushouts of rings

For a cospan `X ⟶ Z ⟵ Y` of profinite sets with (explicit) pullback `P = X ×_Z Y`, the square
of rings of locally constant integer-valued functions
```
LC(Z, ℤ) ⟶ LC(X, ℤ)
   ↓          ↓
LC(Y, ℤ) ⟶ LC(P, ℤ)
```
is a pushout (`Profinite.isPushout_locallyConstant_pullback`). Ring maps `LC(S, ℤ) ⟶ A` are
continuous maps `Spec A → S` (`LocallyConstant.liftPrimeSpectrum_specMap`), so this is the
universal property of `P` tested against the spaces `Spec A`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Profinite

variable {X Y Z : Profinite.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The ring map `LC(T, ℤ) ⟶ LC(S, ℤ)` given by precomposition with `h : S ⟶ T`. -/
noncomputable abbrev locallyConstantMap {S T : Profinite.{u}} (h : S ⟶ T) :
    CommRingCat.of (LocallyConstant T ℤ) ⟶ CommRingCat.of (LocallyConstant S ℤ) :=
  CommRingCat.ofHom (LocallyConstant.comapRingHom h.hom.hom)

lemma specMap_mem_pullback {A : Type u} [CommRing A] (a : LocallyConstant X ℤ →+* A)
    (b : LocallyConstant Y ℤ →+* A)
    (h : a.comp (LocallyConstant.comapRingHom f.hom.hom) =
      b.comp (LocallyConstant.comapRingHom g.hom.hom)) (p : PrimeSpectrum A) :
    f (LocallyConstant.specMap a p) = g (LocallyConstant.specMap b p) := by
  have h' := congrArg (fun φ ↦ LocallyConstant.specMap φ p) h
  simp only [LocallyConstant.specMap_comp_comapRingHom] at h'
  exact h'

/-- The continuous map `Spec A → X ×_Z Y` induced by two ring maps `LC(X, ℤ) → A` and
`LC(Y, ℤ) → A` agreeing on `LC(Z, ℤ)`. -/
noncomputable def pullbackSpecMap {A : Type u} [CommRing A] (a : LocallyConstant X ℤ →+* A)
    (b : LocallyConstant Y ℤ →+* A)
    (h : a.comp (LocallyConstant.comapRingHom f.hom.hom) =
      b.comp (LocallyConstant.comapRingHom g.hom.hom)) :
    C(PrimeSpectrum A, CompHausLike.pullback f g) :=
  ⟨fun p ↦ ⟨(LocallyConstant.specMap a p, LocallyConstant.specMap b p),
      specMap_mem_pullback f g a b h p⟩,
    ((LocallyConstant.specMap a).continuous.prodMk
      (LocallyConstant.specMap b).continuous).subtype_mk _⟩

lemma hom_comp_locallyConstantMap {S T : Profinite.{u}} (h : S ⟶ T) {A : CommRingCat.{u}}
    (φ : CommRingCat.of (LocallyConstant S ℤ) ⟶ A) :
    (locallyConstantMap h ≫ φ).hom = φ.hom.comp (LocallyConstant.comapRingHom h.hom.hom) :=
  rfl

/-- `LocallyConstant (-, ℤ)` sends the explicit pullback of profinite sets to a pushout of
rings. -/
lemma isPushout_locallyConstant_pullback :
    IsPushout (locallyConstantMap f) (locallyConstantMap g)
      (locallyConstantMap (CompHausLike.pullback.fst f g))
      (locallyConstantMap (CompHausLike.pullback.snd f g)) := by
  have hcomm : locallyConstantMap f ≫ locallyConstantMap (CompHausLike.pullback.fst f g) =
      locallyConstantMap g ≫ locallyConstantMap (CompHausLike.pullback.snd f g) := by
    ext φ ⟨⟨x, y⟩, hxy⟩
    exact congrArg φ hxy
  have hs (s : PushoutCocone (locallyConstantMap f) (locallyConstantMap g)) :
      s.inl.hom.comp (LocallyConstant.comapRingHom f.hom.hom) =
        s.inr.hom.comp (LocallyConstant.comapRingHom g.hom.hom) :=
    congrArg CommRingCat.Hom.hom s.condition
  let σ (s : PushoutCocone (locallyConstantMap f) (locallyConstantMap g)) :=
    pullbackSpecMap f g s.inl.hom s.inr.hom (hs s)
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hcomm) ?_
  refine PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (LocallyConstant.liftPrimeSpectrum (Int.castRingHom _) (σ s)))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)
  · refine CommRingCat.hom_ext (LocallyConstant.ringHom_ext_of_specMap (RingHom.ext_int _ _) ?_)
    rw [hom_comp_locallyConstantMap, CommRingCat.hom_ofHom,
      LocallyConstant.specMap_comp_comapRingHom, LocallyConstant.specMap_liftPrimeSpectrum]
    rfl
  · refine CommRingCat.hom_ext (LocallyConstant.ringHom_ext_of_specMap (RingHom.ext_int _ _) ?_)
    rw [hom_comp_locallyConstantMap, CommRingCat.hom_ofHom,
      LocallyConstant.specMap_comp_comapRingHom, LocallyConstant.specMap_liftPrimeSpectrum]
    rfl
  · refine CommRingCat.hom_ext (LocallyConstant.ringHom_ext_of_specMap (RingHom.ext_int _ _) ?_)
    rw [CommRingCat.hom_ofHom, LocallyConstant.specMap_liftPrimeSpectrum]
    refine ContinuousMap.ext fun p ↦ Subtype.ext (Prod.ext ?_ ?_)
    · have h := congrArg (fun φ ↦ LocallyConstant.specMap (CommRingCat.Hom.hom φ) p) h₁
      simp only [hom_comp_locallyConstantMap, LocallyConstant.specMap_comp_comapRingHom] at h
      exact h
    · have h := congrArg (fun φ ↦ LocallyConstant.specMap (CommRingCat.Hom.hom φ) p) h₂
      simp only [hom_comp_locallyConstantMap, LocallyConstant.specMap_comp_comapRingHom] at h
      exact h

end Profinite
