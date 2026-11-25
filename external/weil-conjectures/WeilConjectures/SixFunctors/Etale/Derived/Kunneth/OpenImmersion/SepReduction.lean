/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Torsion

/-!
# Reduction to a separably closed ground field

Let `K` be a field, `j : U ⟶ X` an open immersion of `K`-schemes, `q₁ : W ⟶ X` a morphism and
`V = U ×_X W`, with projections `e : V ⟶ U` and `h : V ⟶ W`. For a field extension `L / K`
(for instance a separable closure of `K`), base change along `Spec L ⟶ Spec K` gives a cube

```
V_L --e_L--> U_L          V_L ---> V          U_L ---> U
 |            |            |       |           |       |
h_L          j_L          h_L      h          j_L      j
 v            v            v       v           v       v
W_L --q_L--> X_L          W_L ---> W          X_L ---> X
```

By the base change along field extensions (blueprint `corollary-open-direct-image-over-field--2`,
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`) the base change maps of
the two side faces are isomorphisms, so by the compatibility of base change maps with further
base change (blueprint `corollary-open-direct-image-over-field--2`,
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_cube_of_surjective`) and the
conservativity of the pullback along the surjective morphism `W_L ⟶ W` (blueprint
`lem-kun-sep-closure-conservative`), the base change map of the original square is an isomorphism
as soon as the one of the base changed square is (blueprint
`corollary-open-direct-image-over-field--2`,
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIso_fieldExtension`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `corollary-open-direct-image-over-field--2`: **reduction to a separably closed ground
field.**

Let `K` be a field, `j : U ⟶ X` a quasi-compact open immersion over `K`, `q₁ : W ⟶ X` and
`V = U ×_X W` with projections `e : V ⟶ U`, `h : V ⟶ W` (the square `sq`). Let `L / K` be a
field extension (in the blueprint `L = K^sep`) and consider the base change of everything to
`L`: `X_L = X ×_K L`, `U_L = U ×_X X_L`, `W_L = W ×_X X_L`, `V_L = V ×_W W_L`, with the base
changed square `sq'`. Let `n` be invertible in `K` and kill `Λ`. If the degree-`i` base change
map of `sq'` at the pullback `F_L` of `F` is an isomorphism, then so is the degree-`i` base
change map `q₁⁻¹ R^i j_* F ⟶ R^i h_* e⁻¹ F` of `sq` at `F`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isIso_fieldExtension {K L : Type u} [Field K]
    [Field L] [Algebra K L] {X U W V X' U' W' V' : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (q₁ : W ⟶ X) (e : V ⟶ U) (h : V ⟶ W)
    (sq : IsPullback e h j q₁) (u : X' ⟶ X) (aX' : X' ⟶ Spec (.of L))
    (hX : IsPullback u aX' aX (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (uU : U' ⟶ U) (j' : U' ⟶ X') (hU : IsPullback uU j' j u)
    (uW : W' ⟶ W) (q₁' : W' ⟶ X') (hW : IsPullback uW q₁' q₁ u)
    (uV : V' ⟶ V) (e' : V' ⟶ U') (h' : V' ⟶ W') (hV : IsPullback uV h' h uW)
    (sq' : IsPullback e' h' j' q₁') (he : e' ≫ uU = uV ≫ e) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : IsIso (Etale.baseChangeHomologyMap Λ sq' i ((uU)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq i F) := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hnK : (n : K) ≠ 0 := hn.ne_zero
  have := Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero n hn₀ hΛ hnK F
  have := Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero n hn₀ hΛ hnK
    ((e)^*[ModuleCat.{u + 1} Λ].obj F)
  have : QuasiCompact h := MorphismProperty.of_isPullback sq ‹QuasiCompact j›
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq inferInstance
  have hsurj : Surjective uW := by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
      ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    have : Surjective u := MorphismProperty.of_isPullback hX.flip this
    exact MorphismProperty.of_isPullback hW.flip this
  exact Etale.isIso_baseChangeHomologyMap_of_cube_of_surjective Λ sq hU sq' hV hW.w.symm he
    hsurj.surj i F
    (Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ aX j u aX' hX hU i F)
    (Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ (q₁ ≫ aX) h uW (q₁' ≫ aX')
      (hW.paste_vert hX) hV i _) H

end AlgebraicGeometry
