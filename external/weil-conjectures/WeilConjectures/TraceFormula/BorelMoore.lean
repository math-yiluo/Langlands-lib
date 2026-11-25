/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.Dualizing

/-!

# Pushforward and linearity of Borel–Moore sections

Let `h : T ⟶ T'` be a proper morphism of separated `k`-schemes of finite type. The
*pushforward* of a Borel–Moore section `α : ℚ̄_ℓ,T ⟶ ω_T` is the Borel–Moore section
```
h_* α : ℚ̄_ℓ,T' ⟶ Rh_* Lh^* ℚ̄_ℓ,T' ≅ Rh_* ℚ̄_ℓ,T --Rh_* α--> Rh_* ω_T ≅ Rh_! Rh^! ω_T' ⟶ ω_T'
```
(`ProEtale.CondensedRing.BorelMooreSection.pushforward`, blueprint
`definition-pushforward-correspondence--2`), built from the unit of `Lh^* ⊣ Rh_*`, the unit
isomorphism of the monoidal functor `Lh^*`, the identification `Rh_! ≅ Rh_*` of the proper `h`, the
composition isomorphism `Rh^! ω_T' ≅ ω_T` and the counit of `Rh_! ⊣ Rh^!`.

The scalars `End (ℚ̄_ℓ,s)` act on the Borel–Moore sections of `T` through the monoidal pullback
`La_T^*` (`ProEtale.CondensedRing.BorelMooreSection.scalar`), and the integral is linear for
this action (`ProEtale.CondensedRing.BorelMooreSection.integral_scalar_comp`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--3`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace BorelMooreSection

section Pushforward

variable {T T' : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
  [IsSeparated T.hom] [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom] [IsSeparated T'.hom]
  (h : T ⟶ T') [IsProper h.left]

/-- The *pushforward* `h_* α` of a Borel–Moore section `α` along a proper morphism `h`
(blueprint `definition-pushforward-correspondence--2`):
```
ℚ̄_ℓ,T' ⟶ Rh_* Lh^* ℚ̄_ℓ,T' ≅ Rh_* ℚ̄_ℓ,T --Rh_* α--> Rh_* ω_T ≅ Rh_! ω_T ≅ Rh_! Rh^! ω_T'
  ⟶ ω_T'.
```
-/
noncomputable def pushforward (α : BorelMooreSection ℓ T) : BorelMooreSection ℓ T' :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ h).unit.app
      (𝟙_ _) ≫
    (boundedConstructibleLowerStar ℓ h).map
      ((Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h)).inv ≫ α) ≫
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv.app _ ≫
    (boundedConstructibleLowerShriek ℓ h).map
      (dualizingComplexComp ℓ h).inv ≫
    (boundedConstructibleUpperShriekAdjunction ℓ h).counit.app _

/-- The pushforward of Borel–Moore sections is additive. -/
lemma pushforward_add (α β : BorelMooreSection ℓ T) :
    pushforward h (α + β) = pushforward h α + pushforward h β := by
  simp only [pushforward, Preadditive.comp_add, Functor.map_add, Preadditive.add_comp]

end Pushforward

section Scalar

variable {X : Over (Spec (.of k))} [QuasiCompact X.hom]

/-- The action of a scalar `t ∈ End (ℚ̄_ℓ,s)` on `ℚ̄_ℓ,X`: the pullback of `t` along the structure
morphism `a_X`, read through the unit isomorphism `ℚ̄_ℓ,X ≅ La_X^* ℚ̄_ℓ,s` of the monoidal functor
`La_X^*`. -/
noncomputable def scalar [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    (t : End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))) :
    End (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  .of ((Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map t.asHom ≫
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).inv)

/-- **Linearity of the integral** (blueprint `theorem-proper-pushforward-lefschetz-verdier--3`,
`definition-trace-class-local-terms--2`): for a scalar `t ∈ End (ℚ̄_ℓ,s)` acting on a Borel–Moore
section `α` through `scalar`, `∫_X (t • α) = t ∘ ∫_X α`. Together with `integral_add` this is the
`End (ℚ̄_ℓ,s)`-linearity of the integral. -/
lemma integral_scalar_comp [IsProper X.hom]
    (t : End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (α : BorelMooreSection ℓ X) :
    integral ((scalar t).asHom ≫ α : BorelMooreSection ℓ X) =
      .of (t.asHom ≫ α.integral.asHom) := by
  apply End.ext
  have : IsProper (toPoint X).left := by
    rw [toPoint_left]
    infer_instance
  have hn := (boundedConstructibleUpperStarLowerStarAdjunction ℓ
    (toPoint X)).unit.naturality t.asHom
  simp only [Functor.id_map, Functor.comp_map] at hn
  simp only [integral, scalar, Adjunction.homEquiv_counit, Category.assoc, Functor.map_comp]
  rw [← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.naturality_assoc
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).hom,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.naturality_assoc,
    ← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.naturality_assoc,
    ← reassoc_of% hn]

end Scalar

end BorelMooreSection

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace BorelMooreSection

variable {X : Over (Spec (.of k))} [QuasiCompact X.hom]

-- the conjugation steps unfold the restricted `ℚ̲̄_ℓ`-functors, which is expensive
variable [LocallyOfFiniteType X.hom] [IsSeparated X.hom] in
/-- The counit coherence of `lowerShriek_map_dualizingComplexComp_inv_counit`, for a morphism
`f : X ⟶ s` and an endomorphism `b = 𝟙` of the base point in place of the structure
morphisms. -/
private lemma lowerShriek_map_upperShriekComp_counit_aux (f : X ⟶ point k)
    (b : point k ⟶ point k) (hb : b = 𝟙 (point k)) :
    (boundedConstructibleLowerShriek ℓ f).map
        ((((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f b).app (𝟙_ _)).symm ≪≫
          eqToIso (by rw [hb, Category.comp_id])).inv) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _ ≫
        (upperShriekUnitIsoOfEqId ℓ b hb).hom =
    (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app _ := by
  subst hb
  have e : (upperShriekUnitIsoOfEqId ℓ (𝟙 (point k)) rfl).hom =
      ((boundedConstructibleUpperShriekId ℓ (point k)).app (𝟙_ _)).hom := by
    simp [upperShriekUnitIsoOfEqId]
  rw [e]
  have h := conjugateIsoEquiv_comp_unit_counit
    (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ 𝟙 (point k)))
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 (point k)))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 (point k)))
    (boundedConstructibleLowerShriekId ℓ (point k))
    (eqToIso (congrArg (boundedConstructibleLowerShriek ℓ) (Category.comp_id f)))
    (fun K ↦ by
      rw [boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
        eqToHom_app]
      exact boundedConstructibleLowerShriekComp_padicAlgCl_id_right ℓ f K)
    (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  rw [← boundedConstructibleUpperShriekComp_padicAlgCl.eq_1] at h
  rw [Iso.trans_inv, eqToIso.inv, Iso.symm_inv, Iso.app_hom, Functor.map_comp, Category.assoc]
  refine Eq.trans (congrArg (_ ≫ ·) h) ?_
  rw [eqToIso.inv, eqToHom_app]
  exact Adjunction.counit_eqToHom_family
    (fun m ↦ boundedConstructibleLowerShriek ℓ m)
    (fun m ↦ boundedConstructibleUpperShriek ℓ m)
    (fun m ↦ boundedConstructibleUpperShriekAdjunction ℓ m)
    (Category.comp_id f) _

variable [LocallyOfFiniteType X.hom] [IsSeparated X.hom] in
/-- The composition isomorphism `R(a_X)^! ω_s ≅ ω_X` of the dualizing complexes, followed by
`ω_X = Ra_X^! ℚ̄_ℓ,s ≅ Ra_X^! ω_s` through `ω_s ≅ ℚ̄_ℓ,s`, is compatible with the counits:
the counit of `Ra_{X!} ⊣ Ra_X^!` at `ω_s`, read through `ω_s ≅ ℚ̄_ℓ,s`, is the counit at
`ℚ̄_ℓ,s`. This is the unit coherence of the composition isomorphisms of the exceptional
functors, by conjugation from `boundedConstructibleLowerShriekComp_padicAlgCl_id_right`. -/
lemma lowerShriek_map_dualizingComplexComp_inv_counit :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        (dualizingComplexComp ℓ (toPoint X)).inv ≫
      (boundedConstructibleUpperShriekAdjunction ℓ
        (toPoint X)).counit.app _ ≫ (dualizingComplexPointIso ℓ k).hom =
    (boundedConstructibleUpperShriekAdjunction ℓ
        (toPoint X)).counit.app _ :=
  lowerShriek_map_upperShriekComp_counit_aux (toPoint X) (toPoint (point k)) (toPoint_ext _ _)

instance isProper_toPoint_left [IsProper X.hom] : IsProper (toPoint X).left := by
  rw [toPoint_left]
  infer_instance

/-- **Integration is pushforward to the point** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--2`): for `X` proper over `s`, the integral `∫_X α` is
the pushforward `(a_X)_* α` along the structure morphism, read through `ω_s ≅ ℚ̄_ℓ,s`. -/
theorem integral_eq_pushforward [IsProper X.hom] (α : BorelMooreSection ℓ X) :
    α.integral = .of (pushforward (toPoint X) α ≫ (dualizingComplexPointIso ℓ k).hom) := by
  apply End.ext
  dsimp only [integral, pushforward]
  rw [Adjunction.homEquiv_counit, Functor.map_comp]
  simp only [Category.assoc]
  rw [(boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (toPoint X)).inv.naturality_assoc α, lowerShriek_map_dualizingComplexComp_inv_counit]

/-- **Integration is pushforward to the point**, in the form `∫_X α = ∫_s (a_X)_* α`
(blueprint `theorem-proper-pushforward-lefschetz-verdier--2`). -/
theorem integral_eq_integral_pushforward [IsProper X.hom] (α : BorelMooreSection ℓ X) :
    α.integral = (pushforward (toPoint X) α).integral := by
  rw [integral_point, integral_eq_pushforward]

end BorelMooreSection

end AlgebraicGeometry.ProEtale.CondensedRing
