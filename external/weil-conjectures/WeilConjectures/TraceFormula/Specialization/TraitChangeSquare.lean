/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.TraceFormula.Specialization.TraitChangeTrait

/-!

# Pullback exchanges through a square of proper exchanges

For a commutative square of morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`, `ψ' : P ⟶ P₁`,
`φ₁ : P₁ ⟶ M₁`, the square law of the pushforward exchanges
(`NearbyCyclesModel.pushforwardExchange_square_aux`) shows that the pullback exchange of `φ₀` is
invertible at `A` as soon as the pushforward exchanges of `ψ` and `ψ'`, the base change morphisms
of the squares of bases and of special fibres and the pullback exchange of `φ₁` are invertible at
the relevant objects, and the pushforward along the map of special fibres of `ψ'` reflects
isomorphisms (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_square`). For
`ℚ̄_ℓ`-coefficients, proper base change and the proper exchange supply two of these inputs
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_square_of_isProper`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

/-! ### The square argument -/

section Square

variable {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'}

variable (ℓ : ℕ) [Fact ℓ.Prime]

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

/-- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_square` for `ℚ̄_ℓ`-coefficients, with
the base change morphism of the square of bases and the pushforward exchange of `ψ'` invertible by
proper base change (blueprint `proposition-proper-direct-image-constructible-complexes`) and by the
proper exchange (blueprint `prose-E-03` (2)): it suffices that the square of bases is
cartesian with `g` proper and with noetherian bases over fields `k₁` and `k₂` in which `ℓ` is
invertible, that `P` and `P₁` are models of finite type over the trait `Spec k₀⟦t⟧` with `ℓ`
invertible in `k₀`, that `ψ'` is proper and cartesian on special fibres and identifications, and
that `A` is bounded constructible. -/
theorem Hom.isIso_pullbackExchange_app_of_square_of_isProper {k₀ k₁ k₂ : Type u} [Field k₀]
    [Field k₁] [Field k₂] [Fact (ringChar k₀ ≠ ℓ)] [Fact (ringChar k₁ ≠ ℓ)]
    [Fact (ringChar k₂ ≠ ℓ)] [IsNoetherian X₁] [IsNoetherian Z₁] (a₁ : X₁ ⟶ Spec (.of k₁))
    (a₂ : Z₁ ⟶ Spec (.of k₂)) (hP : ∃ a : Z' ⟶ Spec (.of k₀), P.IsTraitModel (X' := Over.mk a))
    (hP₁ : ∃ a : Z₁' ⟶ Spec (.of k₀), P₁.IsTraitModel (X' := Over.mk a)) (φ₀ : P.Hom M f₀ f₀')
    (ψ : M.Hom M₁ g g') (ψ' : P.Hom P₁ k k') (φ₁ : P₁.Hom M₁ e e')
    (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e') [IsProper g] (hpb : IsPullback f₀ k g e) [IsProper ψ'.total]
    [IsProper k] (hi' : IsPullback P.i k' ψ'.total P₁.i)
    (hε' : IsPullback P.ε ψ'.generic k P₁.ε)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝐐 X)))
    (hA : boundedConstructible (condensedRingObj 𝐐 X) A)
    (hχ : IsIso ((ψ.pushforwardExchange 𝐐).app A))
    (hbc' : IsIso ((baseChangeMap 𝐐 ⟨hs⟩).app ((M.nearbyCycles 𝐐).obj A)))
    (hα₁ : IsIso ((φ₁.pullbackExchange 𝐐).app (R((g)_*⟦𝐐⟧).obj A)))
    (hR : ∀ {U V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
      (condensedRingObj 𝐐 Z'))} (a : U ⟶ V), IsIso (R((k')_*⟦𝐐⟧).map a) → IsIso a) :
    IsIso ((φ₀.pullbackExchange 𝐐).app A) := by
  have hbc := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ a₁ a₂ ⟨hb⟩ hpb A
    hA
  have hχ' := ψ'.isIso_pushforwardExchange_app_of_isProper a₂ hP hP₁ hi' hε'
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₀ A hA)
  exact_mod_proofs φ₀.isIso_pullbackExchange_app_of_square 𝐐 ψ ψ' φ₁ htot hgen hb hs A
    (by exact_mod_proofs hχ) (by exact_mod_proofs hbc') (by exact_mod_proofs hα₁)
    (by exact_mod_proofs hbc) (by exact_mod_proofs hχ') (fun a h ↦ by exact_mod_proofs hR a h)

end Square

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
