/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRationalTrivialization
public import WeilConjectures.WeilSheaf.TateFrobeniusTrivialization

/-! # The Frobenius scalar after rationalizing a Tate trivialization -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X U : Scheme.{u}} (g : U ⟶ X)

/-- Extension of coefficients preserves a scalar relation between trivializations. -/
lemma purityChangeCoefficientTrivialization_hom_zsmul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e e' : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj (𝟙_ _))
    (c : ℤ) (h : e'.hom = c • e.hom) :
    (purityChangeCoefficientTrivialization Λ a g M e').hom =
      c • (purityChangeCoefficientTrivialization Λ a g M e).hom := by
  simp only [purityChangeCoefficientTrivialization, purityChangeCoefficientPullbackIso,
    purityExtendPullbackIso, Iso.trans_hom, Functor.mapIso_hom, h,
    Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] [WeaklyEtale g]
  (f : U ⟶ Spec (.of (AlgebraicClosure k)))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- The rational root trivialization along the semilinear structure is multiplied
by the cardinality of the ground field, just as the integral root trivialization. -/
lemma purityRationalTateTrivialization_comp_specGeometricFrobenius_hom :
    (purityRationalTateTrivialization g (f ≫ (specGeometricFrobenius k).asIso.hom) ℓ hζ hζ').hom =
      (Nat.card k : ℤ) • (purityRationalTateTrivialization g f ℓ hζ hζ').hom := by
  apply purityChangeCoefficientTrivialization_hom_zsmul
  simp only [Iso.trans_hom,
    upperStarMapModTateModuleIsoUnit_comp_specGeometricFrobenius_hom,
    Preadditive.zsmul_comp]

end AlgebraicGeometry.ProEtale
