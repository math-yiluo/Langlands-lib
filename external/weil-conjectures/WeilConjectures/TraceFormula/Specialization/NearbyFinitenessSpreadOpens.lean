/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSpreadEtale

/-!

# Deligne's criterion with the local input on open models

Let `S = Spec k'⟦t⟧` be the strictly henselian trait and `p : P ⟶ S` proper. In the pointwise
form of Deligne's criterion
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint`), the local
input is the bounded constructibility of `Ψ_P (j_! B)` on a neighbourhood of every point `y` of
the special fibre lying over the generic point of a coordinate line. By the open exchange
(`NearbyCyclesModel.boundedConstructible_upperStar_nearbyCycles_iff_of_weaklyEtale`), it suffices
to find an open `V ⊆ P` containing `y` such that the nearby cycles `Ψ_V ((j_! B)|_V)` of the open
model `V`, a separated scheme of finite type over `S`, are bounded constructible
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint_of_opens`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Local input from open models**: let `p : P ⟶ S` be a scheme over the trait, `C = Ψ_P B'`
and `w` a point of the special fibre `P_s`. If an open `V ⊆ P` contains (the image of) `w` and
the nearby cycles `Ψ_V (B'|_V)` of the open model `V` are bounded constructible, then `C` is
bounded constructible on the open neighbourhood `V_s` of `w`, and so on every neighbourhood of `w`
inside `V_s`. -/
theorem boundedConstructible_upperStar_nearbyCycles_of_opens {P Y : Scheme.{u}}
    (p : P ⟶ trait k') (f : Y ⟶ (traitStdSpecialFibre p).left) (V : P.Opens)
    (hf : Set.range f ⊆ (traitStdModel p).i ⁻¹' (V : Set P))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P))}
    (hV : boundedConstructible _
      (((traitStdModel (V.ι ≫ p)).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((L((V.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B))) :
    boundedConstructible _ ((L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      (((traitStdModel p).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B)) := by
  refine boundedConstructible_leftDerivedUpperStar_of_range_subset
    (Profinite.padicAlgClRingObj ℓ) f (traitStdEtaleSpecial p V.ι) ?_
    ((boundedConstructible_upperStar_nearbyCycles_iff_of_weaklyEtale p V.ι _ B).2 hV)
  rw [range_traitStdEtaleSpecial, Scheme.Opens.range_ι]
  exact hf

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Deligne's criterion through a compactification, with the local input on open models**
(SGA 4½, [Th. finitude], proof of 3.2): let `q : T ⟶ S` factor as an open immersion
`j : T ⟶ P` followed by a proper `p : P ⟶ S`, and `B` be bounded constructible on `T`. Suppose
that every point of the special fibre `P_s` has an open neighbourhood `U` with finitely many
coordinates `bᵢ : U ⟶ 𝔸¹_{k'}` locally of finite type, jointly detecting closed points, such that
every point `v` of `U` over the generic point of a coordinate line lies in an open `V ⊆ P` whose
open model has bounded constructible nearby cycles `Ψ_V ((j_! B)|_V)`. Then `Ψ_T B` is bounded
constructible
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint` and
`NearbyCyclesModel.boundedConstructible_upperStar_nearbyCycles_of_opens`). -/
theorem boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint_of_opens
    {T P : Scheme.{u}} (q : T ⟶ trait k') (j : T ⟶ P) [IsOpenImmersion j] (p : P ⟶ trait k')
    [IsProper p] (hjp : j ≫ p = q)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))}
    (hB : boundedConstructible _ B)
    (H : ∀ y : (traitStdSpecialFibre p).left, ∃ (U : (traitStdSpecialFibre p).left.Opens)
      (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')))),
      (∀ i, LocallyOfFiniteType (b i)) ∧ (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i (v : U), IsGenericPoint (b i v) Set.univ →
        ∃ V : P.Opens, (traitStdModel p).i v.1 ∈ V ∧ boundedConstructible _
          (((traitStdModel (V.ι ≫ p)).geometric.nearbyCycles
            (Profinite.padicAlgClRingObj ℓ)).obj
              ((L((V.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
                ((D((j)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B)))) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre q).left)
      (((traitStdModel q).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B) := by
  refine boundedConstructible_nearbyCycles_traitStdModel_of_isGenericPoint q j p hjp hB
    fun y ↦ ?_
  obtain ⟨U, hyU, ι, hι, b, hb, hcl, hgen⟩ := H y
  refine ⟨U, hyU, ι, hι, b, hb, hcl, fun i v hv ↦ ?_⟩
  obtain ⟨V, hvV, hV⟩ := hgen i v hv
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ ((traitStdModel p).i ⁻¹ᵁ V)
  refine ⟨W, hvV, ?_⟩
  refine (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarComp
    (Profinite.padicAlgClRingObj ℓ) W.ι U.ι).app _) ?_
  refine boundedConstructible_upperStar_nearbyCycles_of_opens p _ V ?_ hV
  rintro _ ⟨w, rfl⟩
  exact w.2

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
