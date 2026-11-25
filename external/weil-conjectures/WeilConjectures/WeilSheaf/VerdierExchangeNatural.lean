/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierExchange
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.Localization

/-!
# The Verdier exchange of Weil complexes, natural form

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the Verdier exchange `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X` (blueprint
`lemma-internal-adjunction-two-exchange-formulas--2`) as a natural isomorphism of functors
`(WeilComplex X)ᵒᵖ ⥤ WeilComplex Y`. With Verdier biduality it identifies `Rf^!` with `𝔻_X f^* 𝔻_Y`
(`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`).

The Verdier dual `AlgebraicGeometry.WeilComplex.verdierDual` and the dualizing complex are defined
in `WeilConjectures.WeilSheaf.VerdierDual`, which imports this file; they are spelled out here:
the dualizing complex of `X` is `(Ra_X!)^{ra}(ℚ̄_ℓ)`, the right adjoint of `Ra_X!` applied to the
constant Weil sheaf on `Spec k₀`, and the Verdier dual is the derived internal hom into it, lifted
to Weil complexes along a proof that it lands there (in `VerdierDual`,
`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom_dualizingComplex`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable (k₀ l) in
/-- The dualizing complex `ω_X = (Ra_X!)^{ra}(ℚ̄_ℓ)` of a `k₀`-scheme of finite type `X`, given a
right adjoint of `Ra_X!` (`AlgebraicGeometry.WeilComplex.dualizingComplex`, spelled out). -/
noncomputable abbrev dualizingComplexOfIsLeftAdjoint (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint] :
    WeilComplex k₀ l X :=
  (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).rightAdjoint.obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [(derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]
  [(derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).IsLeftAdjoint]

/-- **Verdier exchange, natural in `M`** (blueprint
`lemma-internal-adjunction-two-exchange-formulas--2`): for a separated morphism of finite type
`f : X ⟶ Y`, `𝔻_Y (Rf₀! M) ≅ Rf_* (𝔻_X M)` naturally in the Weil complex `M`. Here `𝔻 = RHom(-, ω)`
is the derived internal hom into the dualizing complex `ω = (Ra!)^{ra}(ℚ̄_ℓ)`, lifted to Weil
complexes along any proofs `hX`, `hY` that it lands there.

This is the case `S = Spec k₀`, `Q = ℚ̄_ℓ` of
`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_op_comp_iso_of_adjunction`; the
objectwise form is `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`. -/
theorem nonempty_verdierDual_derivedLowerShriek_natIso
    (hX : ∀ K : WeilComplex k₀ l X, WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplexOfIsLeftAdjoint k₀ l X).obj).obj
        (op K.obj)))
    (hY : ∀ K : WeilComplex k₀ l Y, WeilComplex.objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.derivedHom k₀ l Y (dualizingComplexOfIsLeftAdjoint k₀ l Y).obj).obj
        (op K.obj))) :
    Nonempty ((derivedLowerShriek k₀ l f).op ⋙
        ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (dualizingComplexOfIsLeftAdjoint k₀ l Y).obj)
          (fun K ↦ hY K.unop) ≅
      ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplexOfIsLeftAdjoint k₀ l X).obj)
          (fun K ↦ hX K.unop) ⋙ derivedLowerStar f) :=
  nonempty_derivedLowerShriek_op_comp_iso_of_adjunction f _ _ (comp_over f _)
    (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _) _ hX hY

end WeilComplex

end AlgebraicGeometry
