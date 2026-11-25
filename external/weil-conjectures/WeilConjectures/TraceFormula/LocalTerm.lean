/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ClopenIdempotent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek
public import WeilConjectures.TraceFormula.BorelMoore
public import WeilConjectures.TraceFormula.OpenCover

/-!

# Local terms of Borel–Moore sections

Let `X` be a scheme proper over `s = Spec k` and `j : B ⟶ X` the inclusion of an open and
closed subscheme. This file relates the local term `LT_B(α) = ∫_B j^* α` of a Borel–Moore
section `α : ℚ̄_ℓ,X ⟶ ω_X` (`ProEtale.CondensedRing.BorelMooreSection.localTerm`) to the
integral over `X`, and proves that the integral over a finite disjoint union of open and closed
pieces is the sum of the local terms.

## Functoriality of the pushforward

For proper morphisms `f : T ⟶ T'` and `g : T' ⟶ T''` the pushforward of Borel–Moore sections
is functorial, `g_* (f_* γ) = (f ≫ g)_* γ`
(`ProEtale.CondensedRing.BorelMooreSection.pushforward_comp`): this is the compatibility of the
composition isomorphisms of `Lf^*`, `Rf_*`, `Rf_!` and `Rf^!` with the units, with the
identifications `Rf_! ≅ Rf_*` and with each other. Together with
`ProEtale.CondensedRing.BorelMooreSection.integral_eq_pushforward` it shows that the integral is
invariant under proper pushforward, `∫_X h_* γ = ∫_T γ`
(`ProEtale.CondensedRing.BorelMooreSection.integral_pushforward`).

## The idempotent of an open and closed subscheme

The open and closed subscheme `j : B ⟶ X` cuts out the endomorphism
```
e_B : L ⟶ Rj_* Lj^* L ≅ Rj_* Rj^! L ≅ Rj_! Rj^! L ⟶ L
```
of the identity functor of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the unit of `Lj^* ⊣ Rj_*` followed by the counit of
`Rj_! ⊣ Rj^!` (`ProEtale.CondensedRing.clopenIdempotent`, blueprint
`definition-trace-class-local-terms--3`). The pushforward of the restriction of `α` to `B` is
`α ∘ e_B`, so that `LT_B(α) = ∫_X α ∘ e_B`
(`ProEtale.CondensedRing.BorelMooreSection.localTerm_eq_integral`). For a decomposition of `X` into
finitely many open and closed pieces `B_β`, the idempotents are orthogonal and sum to the identity
(`ProEtale.CondensedRing.sum_clopenIdempotent_app`): their pullbacks to each piece are detected
by the finite-cover detection of `WeilConjectures.TraceFormula.OpenCover`. Hence
`∫_X α = ∑_β LT_{B_β}(α)`
(`ProEtale.CondensedRing.BorelMooreSection.integral_eq_sum_localTerm`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--3`).

## Sorried input

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen`: for an
  open and closed immersion `j`, the identification `Rj_! ≅ Rj_*` of the proper morphism `j`,
  composed with `Rj_! ≅ j_!` of the open immersion `j`, is the canonical map `j_! ⟶ Rj_*`
  adjoint to the inverse of the unit of `j_! ⊣ Lj^*`. Both identifications are comparisons of
  the lower shriek attached to different compactifications of `j`, and the statement is the
  compatibility of these comparisons (compactification coherence).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Coherence of the dualizing complexes -/

section Dualizing

variable {T T' T'' : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
  [IsSeparated T.hom] [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom] [IsSeparated T'.hom]
  [LocallyOfFiniteType T''.hom] [QuasiCompact T''.hom] [IsSeparated T''.hom]

variable (ℓ) in
/-- **Associativity of the composition isomorphisms of the exceptional inverse image**, the
conjugate of the associativity of the composition isomorphisms of the lower shriek
(`boundedConstructibleLowerShriekComp_padicAlgCl_assoc`). -/
lemma boundedConstructibleUpperShriekComp_padicAlgCl_assoc {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (f : T ⟶ T') (g : T' ⟶ T'') (h : T'' ⟶ S) (K : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ (f ≫ g) h).hom.app K ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).hom.app
          ((boundedConstructibleUpperShriek ℓ h).obj K) =
      eqToHom (congrArg (fun m ↦
        (boundedConstructibleUpperShriek ℓ m).obj K)
          (Category.assoc f g h)) ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f (g ≫ h)).hom.app K ≫
        (boundedConstructibleUpperShriek ℓ f).map
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ g h).hom.app K) :=
  conjugateIsoEquiv_assoc_aux
    (fun m ↦ boundedConstructibleLowerShriek ℓ m)
    (fun m ↦ boundedConstructibleUpperShriek ℓ m)
    (fun m ↦ boundedConstructibleUpperShriekAdjunction ℓ m)
    (Category.assoc f g h)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ g)
    (boundedConstructibleUpperShriekAdjunction ℓ h)
    (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
    (boundedConstructibleUpperShriekAdjunction ℓ (g ≫ h))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (f ≫ g) h)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (g ≫ h))
    (fun K ↦ boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ f g h K) K

/-- The composition isomorphism `Rf^! ω_{T'} ≅ ω_T` for a morphism to a scheme with an arbitrary
structure morphism `a'`, transported along `f ≫ a' = a`. -/
noncomputable def dualizingComplexCompAux {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (f : T ⟶ T')
    (a' : T' ⟶ S) (a : T ⟶ S) (h : f ≫ a' = a) :
    (boundedConstructibleUpperShriek ℓ f).obj
        ((boundedConstructibleUpperShriek ℓ a').obj
          (𝟙_ (Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) ≅
      (boundedConstructibleUpperShriek ℓ a).obj
        (𝟙_ (Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f a').app _).symm ≪≫
    eqToIso (congrArg (fun m ↦
      (boundedConstructibleUpperShriek ℓ m).obj
        (𝟙_ (Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) h)

lemma dualizingComplexCompAux_comp {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (f : T ⟶ T')
    (g : T' ⟶ T'') (a'' : T'' ⟶ S) (a' : T' ⟶ S) (a : T ⟶ S) (h' : g ≫ a'' = a')
    (h : f ≫ a' = a) (hF : (f ≫ g) ≫ a'' = a) :
    (dualizingComplexCompAux (ℓ := ℓ) f a' a h).inv ≫
        (boundedConstructibleUpperShriek ℓ f).map
          (dualizingComplexCompAux (ℓ := ℓ) g a'' a' h').inv =
      (dualizingComplexCompAux (ℓ := ℓ) (f ≫ g) a'' a hF).inv ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).hom.app
          ((boundedConstructibleUpperShriek ℓ a'').obj
            (𝟙_ (Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  subst h' h
  simp only [dualizingComplexCompAux, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, Iso.app_hom,
    eqToHom_refl, Category.id_comp, boundedConstructibleUpperShriekComp_padicAlgCl_assoc]

/-- The composition isomorphisms of the dualizing complexes are associative:
`Rf^! Rg^! ω_{T''} ≅ Rf^! ω_{T'} ≅ ω_T` is `Rf^! Rg^! ω_{T''} ≅ R(f ≫ g)^! ω_{T''} ≅ ω_T`. -/
lemma dualizingComplexComp_inv_comp (f : T ⟶ T') (g : T' ⟶ T'') :
    (dualizingComplexComp ℓ f).inv ≫
        (boundedConstructibleUpperShriek ℓ f).map
          (dualizingComplexComp ℓ g).inv =
      (dualizingComplexComp ℓ (f ≫ g)).inv ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).hom.app
          (dualizingComplex' ℓ T'') :=
  dualizingComplexCompAux_comp f g (toPoint T'') (toPoint T') (toPoint T) (comp_toPoint g)
    (comp_toPoint f) (comp_toPoint (f ≫ g))

end Dualizing

/-! ### Functoriality of the pushforward -/

namespace BorelMooreSection

section Pushforward

variable {T T' T'' : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
  [IsSeparated T.hom] [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom] [IsSeparated T'.hom]
  [LocallyOfFiniteType T''.hom] [QuasiCompact T''.hom] [IsSeparated T''.hom]

/-- The pushforward only depends on the morphism. -/
lemma pushforward_congr {f g : T ⟶ T'} (e : f = g) [IsProper f.left] [IsProper g.left]
    (γ : BorelMooreSection ℓ T) : pushforward f γ = pushforward g γ := by
  subst e
  rfl

/-- **Functoriality of the pushforward** of Borel–Moore sections along proper morphisms:
`g_* (f_* γ) = (f ≫ g)_* γ`. -/
theorem pushforward_comp (f : T ⟶ T') (g : T' ⟶ T'') [IsProper f.left] [IsProper g.left]
    [IsProper (f ≫ g).left] (γ : BorelMooreSection ℓ T) :
    pushforward g (pushforward f γ) = pushforward (f ≫ g) γ :=
  pushforward_comp_aux
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleUpperShriekAdjunction ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f ≫ g))
    (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g)
    (boundedConstructibleLowerStarComp ℓ f g)
    (by rw [boundedConstructibleLowerStarComp, Iso.symm_inv, conjugateIsoEquiv_apply_hom,
      Iso.symm_hom])
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
    (fun K ↦ boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ f g K)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g))
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g)))
    (boundedConstructibleUpperStarComp_hom_app_unit ℓ f g)
    (dualizingComplexComp ℓ f) (dualizingComplexComp ℓ g) (dualizingComplexComp ℓ (f ≫ g))
    (lowerShriekComp_dualizingComplexComp_counit_aux
      (boundedConstructibleUpperShriekAdjunction ℓ f)
      (boundedConstructibleUpperShriekAdjunction ℓ g)
      (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
      (dualizingComplexComp ℓ f) (dualizingComplexComp ℓ g) (dualizingComplexComp ℓ (f ≫ g))
      (dualizingComplexComp_inv_comp f g))
    γ

end Pushforward

end BorelMooreSection

namespace BorelMooreSection

section Integral

variable {T X : Over (Spec (.of k))} [QuasiCompact T.hom] [QuasiCompact X.hom]

variable (ℓ X) in
/-- The integral `∫_X`, as an additive map (blueprint
`theorem-proper-pushforward-lefschetz-verdier--3`). -/
noncomputable def integralAddMonoidHom [IsProper X.hom] :
    BorelMooreSection ℓ X →+ End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  AddMonoidHom.mk' integral integral_add

@[simp]
lemma integralAddMonoidHom_apply [IsProper X.hom] (α : BorelMooreSection ℓ X) :
    integralAddMonoidHom ℓ X α = α.integral :=
  rfl

/-- The integral of the zero section vanishes (blueprint
`theorem-proper-pushforward-lefschetz-verdier--3`). -/
lemma integral_zero [IsProper X.hom] : (0 : BorelMooreSection ℓ X).integral = 0 :=
  (integralAddMonoidHom ℓ X).map_zero

/-- The integral commutes with finite sums (blueprint
`theorem-proper-pushforward-lefschetz-verdier--3`). -/
lemma integral_sum [IsProper X.hom] {ι : Type*} (s : Finset ι) (α : ι → BorelMooreSection ℓ X) :
    (∑ i ∈ s, α i).integral = ∑ i ∈ s, (α i).integral :=
  map_sum (integralAddMonoidHom ℓ X) α s

/-- **Invariance of the integral under proper pushforward**: for a proper morphism `h : T ⟶ X`
of schemes proper over `s`, `∫_X h_* γ = ∫_T γ`. -/
theorem integral_pushforward [IsProper T.hom] [IsProper X.hom] (h : T ⟶ X) [IsProper h.left]
    (γ : BorelMooreSection ℓ T) : (pushforward h γ).integral = γ.integral := by
  have : IsProper (h ≫ toPoint X).left := by
    rw [Over.comp_left]
    infer_instance
  rw [integral_eq_pushforward, integral_eq_pushforward, pushforward_comp,
    pushforward_congr (comp_toPoint h)]

end Integral

end BorelMooreSection

/-! ### The idempotent of an open and closed subscheme -/

section Clopen

variable {B X : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable (ℓ) in
/-- The idempotent `e_B` of an open and closed subscheme `j : B ⟶ X` (blueprint
`definition-trace-class-local-terms--3`): the natural endomorphism
```
L ⟶ Rj_* Lj^* L ≅ Rj_* Rj^! L ≅ Rj_! Rj^! L ⟶ L
```
of the identity functor of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the unit of `Lj^* ⊣ Rj_*` followed by the counit of
`Rj_! ⊣ Rj^!`, through `Rj^! ≅ Lj^*` (open immersion) and `Rj_! ≅ Rj_*` (proper morphism). -/
noncomputable def clopenIdempotent (j : B ⟶ X) [IsOpenImmersion j.left] [IsProper j.left] :
    𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ j).unit ≫
    Functor.whiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).inv
      (boundedConstructibleLowerStar ℓ j) ≫
    Functor.whiskerLeft (boundedConstructibleUpperShriek ℓ j)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv ≫
    (boundedConstructibleUpperShriekAdjunction ℓ j).counit

lemma clopenIdempotent_app (j : B ⟶ X) [IsOpenImmersion j.left] [IsProper j.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (clopenIdempotent ℓ j).app K =
      Adjunction.clopenSection
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ j)
        (boundedConstructibleUpperShriekAdjunction ℓ j)
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j) K ≫
      (boundedConstructibleUpperShriekAdjunction ℓ j).counit.app
        K := by
  rw [clopenIdempotent, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv, Adjunction.clopenSection]
  simp only [Category.assoc]

/-- The pushforward of the restriction `j^* α` of a Borel–Moore section to an open and closed
subscheme `j : B ⟶ X` is `α ∘ e_B`. -/
lemma BorelMooreSection.pushforward_restrict (j : B ⟶ X) [IsOpenImmersion j.left]
    [IsProper j.left] (α : BorelMooreSection ℓ X) :
    BorelMooreSection.pushforward j (α.restrict j) =
      α ≫ (clopenIdempotent ℓ j).app (dualizingComplex' ℓ X) := by
  have hα := (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).inv.naturality α
  rw [BorelMooreSection.pushforward, BorelMooreSection.restrict, clopenIdempotent,
    boundedConstructibleUpperShriekUnitIso_padicAlgCl, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Category.assoc, ← reassoc_of% hα]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc]
  rw [(boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.naturality_assoc
      (dualizingComplexComp ℓ j).hom]
  simp only [Iso.hom_inv_id_map_assoc]
  exact (boundedConstructibleUpperStarLowerStarAdjunction ℓ
    j).unit_naturality_assoc α _

end Clopen

/-! ### Local terms as integrals -/

section LocalTerm

variable {B X : Over (Spec (.of k))} [QuasiCompact B.hom] [QuasiCompact X.hom]

/-- **The local term as an integral over the ambient scheme** (blueprint
`definition-trace-class-local-terms--3`): for an open and closed subscheme `j : B ⟶ X` of a scheme
proper over `s`, `LT_B(α) = ∫_X α ∘ e_B`, for the idempotent `e_B` of `B` (`clopenIdempotent`). -/
theorem BorelMooreSection.localTerm_eq_integral [IsProper X.hom] [IsProper B.hom] (j : B ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left] (α : BorelMooreSection ℓ X) :
    α.localTerm j = BorelMooreSection.integral (X := X)
      ((clopenIdempotent ℓ j).app (𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≫ α) := by
  rw [BorelMooreSection.localTerm, ← BorelMooreSection.integral_pushforward j,
    BorelMooreSection.pushforward_restrict]
  have h := (clopenIdempotent ℓ j).naturality α
  simp only [Functor.id_map, Functor.id_obj] at h
  rw [h]

end LocalTerm

/-! ### Decomposition into local terms -/

section Decomposition

variable {B X : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

variable (ℓ) in
/-- For an open and closed immersion `j`, the identification `Rj_! ≅ Rj_*` of the proper
morphism `j`, composed with the inverse of `Rj_! ≅ j_!` of the open immersion `j`, is the
canonical map `j_! ⟶ Rj_*`, the adjoint of the inverse of the unit `M ⟶ Lj^* j_! M`:
`M ⟶ Lj^* j_! M ≅ Lj^* Rj_! M ≅ Lj^* Rj_* M ⟶ M` is the identity. Both identifications are
comparisons of the lower shriek attached to different compactifications of `j`, and this is the
compatibility of these comparisons (compactification coherence). -/
theorem boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen (j : B ⟶ X)
    [IsOpenImmersion j.left] [IsProper j.left] (M : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app M ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app M ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app M) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        j).counit.app M = 𝟙 M :=
  boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen_of j ℓ
    (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_counit j ℓ) M

/-- The pullback of an extension by zero `Rj_! M` along a morphism whose range misses the range
of the open immersion `j` vanishes. -/
lemma isZero_boundedConstructibleUpperStar_obj_lowerShriek {W : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom] (j : B ⟶ X)
    [IsOpenImmersion j.left] (g : W ⟶ X)
    (hjg : Disjoint (Set.range j.left.base) (Set.range g.left.base))
    (M : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j).obj M)) :=
  (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j g hjg M).of_iso
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).mapIso
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app M))

/-- **The idempotents of a decomposition into open and closed pieces sum to the identity**: if
`X` is the disjoint union of finitely many open and closed subschemes `j_i : B_i ⟶ X`, then
`∑_i e_{B_i} = 𝟙` (blueprint `theorem-proper-pushforward-lefschetz-verdier--3`). -/
theorem sum_clopenIdempotent_app {ι : Type*} [Fintype ι] (B : ι → Over (Spec (.of k)))
    [∀ i, LocallyOfFiniteType (B i).hom] [∀ i, QuasiCompact (B i).hom]
    [∀ i, IsSeparated (B i).hom] (j : ∀ i, B i ⟶ X) [∀ i, IsOpenImmersion (j i).left]
    [∀ i, IsProper (j i).left]
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).left.base)
      (Set.range (j i').left.base))
    (hcover : ⋃ i, Set.range (j i).left.base = Set.univ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∑ i, (clopenIdempotent ℓ (j i)).app K = 𝟙 K := by
  classical
  simp_rw [clopenIdempotent_app]
  set S := fun i ↦ Adjunction.clopenSection
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (j i))
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ (j i))
    (boundedConstructibleUpperShriekAdjunction ℓ (j i))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (j i))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j i)) K with hS
  set R := fun i ↦
    (boundedConstructibleUpperShriekAdjunction ℓ (j i)).counit.app
      K with hR
  have hid (i : ι) : R i ≫ S i = 𝟙 _ :=
    Adjunction.clopenCounit_comp_clopenSection _ _ _ _ _
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen ℓ (j i)) K
  have hzero (i k : ι) (hik : i ≠ k) :
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j k)).map (R i) = 0 :=
    (isZero_boundedConstructibleUpperStar_obj_lowerShriek (j i) (j k) (hdisj hik) _).eq_of_src
      _ _
  have horth (i k : ι) (hik : i ≠ k) : R i ≫ S k = 0 := by
    have hn := (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (j k)).unit.naturality (R i)
    have hz := hzero i k hik
    simp only [Functor.id_map, Functor.comp_map, hR] at hn hz
    simp only [hS, hR, Adjunction.clopenSection]
    rw [reassoc_of% hn, hz]
    simp
  have hiso (k : ι) : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (j k)).map (∑ i, S i ≫ R i)) := by
    rw [Functor.map_sum, Finset.sum_eq_single k (fun i _ hik ↦ by
      rw [Functor.map_comp, hzero i k hik, comp_zero]) (by simp), Functor.map_comp]
    have hRk : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (j k)).map (R k)) :=
      Adjunction.isIso_map_clopenCounit
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ (j k))
        (boundedConstructibleUpperShriekAdjunction ℓ (j k))
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (j k)) K
    have hSk : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j k)).map
        (S k) = inv ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (j k)).map (R k)) :=
      IsIso.eq_inv_of_hom_inv_id (by
        rw [← Functor.map_comp, hid k, CategoryTheory.Functor.map_id]
        rfl)
    rw [hSk]
    infer_instance
  have : IsIso (∑ i, S i ≫ R i) :=
    isIso_of_forall_isIso_boundedConstructibleUpperStar_map _ ℓ j
      (fun x ↦ Set.mem_iUnion.1 (hcover ▸ Set.mem_univ x)) _ hiso
  exact Preadditive.sum_comp_eq_id_of_orthogonal S R hid horth

end Decomposition

namespace BorelMooreSection

variable {X : Over (Spec (.of k))} [QuasiCompact X.hom]

/-- **Decomposition of the integral into local terms** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--3`): if a
scheme `X` proper over `s` is the disjoint union of finitely many open and closed subschemes
`j_β : B_β ⟶ X`, the integral of a Borel–Moore section is the sum of its local terms,
`∫_X α = ∑_β LT_{B_β}(α)`. -/
theorem integral_eq_sum_localTerm [IsProper X.hom] {ι : Type*} [Fintype ι]
    (B : ι → Over (Spec (.of k))) [∀ i, QuasiCompact (B i).hom] [∀ i, IsProper (B i).hom]
    (j : ∀ i, B i ⟶ X) [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).left.base)
      (Set.range (j i').left.base))
    (hcover : ⋃ i, Set.range (j i).left.base = Set.univ) (α : BorelMooreSection ℓ X) :
    α.integral = ∑ i, α.localTerm (j i) := by
  simp_rw [localTerm_eq_integral]
  rw [← integral_sum, ← Preadditive.sum_comp, sum_clopenIdempotent_app B j hdisj hcover,
    Category.id_comp]

end BorelMooreSection

/-! ### Local terms at point components -/

namespace BorelMooreSection

variable {B E : Over (Spec (.of k))} [QuasiCompact B.hom] [LocallyOfFiniteType E.hom]
  [QuasiCompact E.hom] [IsSeparated E.hom]

/-- **The local term at a point component** (blueprint `lemma-local-term-restriction-map--1`,
`lemma-local-term-restriction-map--1`): along an open and closed immersion `j : s ⟶ E` of the base
point, the local term of `α` is its restriction `j^* α : ℚ̄_ℓ,s ⟶ ω_s`, read as an element of
`End (ℚ̄_ℓ,s)` through `ω_s ≅ ℚ̄_ℓ,s`. -/
theorem localTerm_point (j : point k ⟶ E) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (α : BorelMooreSection ℓ E) :
    α.localTerm j = .of (α.restrict j ≫ (dualizingComplexPointIso ℓ k).hom) :=
  integral_point _

/-- **The local term at a point component** (blueprint `lemma-local-term-restriction-map--1`): for
an open and closed subscheme `j : B ⟶ E` with an isomorphism `e : B ≅ s` over `s`, the local term of
`α` is the restriction `j^* α`, transported to the base point along `e` and read as an element
of `End (ℚ̄_ℓ,s)` through `ω_s ≅ ℚ̄_ℓ,s`. -/
theorem localTerm_eq_of_iso [IsProper B.hom] (j : B ⟶ E) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left] (e : B ≅ point k) [IsProper e.hom.left]
    (α : BorelMooreSection ℓ E) :
    α.localTerm j =
      .of (pushforward e.hom (α.restrict j) ≫ (dualizingComplexPointIso ℓ k).hom) := by
  rw [← integral_point, integral_pushforward, localTerm]

end BorelMooreSection


/-! ### Local terms of pushforwards -/

namespace BorelMooreSection

variable {T B X : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The pushforward of a Borel–Moore section along an open and closed immersion `j : B ⟶ X` is
fixed by the idempotent `e_B` of `B`. -/
lemma pushforward_comp_clopenIdempotent (j : B ⟶ X) [IsOpenImmersion j.left] [IsProper j.left]
    (γ : BorelMooreSection ℓ B) :
    pushforward j γ ≫ (clopenIdempotent ℓ j).app (dualizingComplex' ℓ X) =
      pushforward j γ := by
  rw [clopenIdempotent_app, pushforward]
  simp only [Category.assoc]
  rw [reassoc_of% (Adjunction.clopenCounit_comp_clopenSection _ _ _ _ _
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen ℓ j)
    (dualizingComplex' ℓ X))]

/-- The restriction to an open and closed subscheme `j : B ⟶ X` of the pushforward along `j` of
a Borel–Moore section of `B` is the section itself. -/
lemma restrict_pushforward_self (j : B ⟶ X) [IsOpenImmersion j.left] [IsProper j.left]
    (γ : BorelMooreSection ℓ B) : (pushforward j γ).restrict j = γ := by
  have key := Adjunction.conjugateIsoEquiv_inv_app_comp_map_clopenPush
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen ℓ j)
    ((Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).inv ≫ γ)
    (dualizingComplexComp ℓ j).inv
  rw [restrict, pushforward, boundedConstructibleUpperShriekUnitIso_padicAlgCl, Iso.trans_inv,
    Iso.symm_inv, Iso.app_inv, Category.assoc,
    boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl,
    reassoc_of% key]
  simp

end BorelMooreSection

namespace BorelMooreSection

variable {T B X : Over (Spec (.of k))} [QuasiCompact T.hom] [QuasiCompact B.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The local term of a pushforward** (blueprint `proposition-frobenius-local-term-curve--1`, Step
3): for an open and closed subscheme `j : B ⟶ X`, proper over `s`, and a proper morphism `h : T ⟶ X`
from a scheme proper over `s` with image in `B`, the local term along `B` of the Borel–Moore
pushforward `h_* γ` is `∫_T γ`. -/
theorem localTerm_pushforward [IsProper T.hom] [IsProper B.hom] (j : B ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left] (h : T ⟶ X) [IsProper h.left]
    (hh : Set.range h.left.base ⊆ Set.range j.left.base) (γ : BorelMooreSection ℓ T) :
    (pushforward h γ).localTerm j = γ.integral := by
  obtain ⟨e, rfl⟩ : ∃ e : T ⟶ B, e ≫ j = h :=
    ⟨Over.homMk (IsOpenImmersion.lift j.left h.left hh) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w h]),
      Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  have : IsProper e.left := IsProper.of_comp e.left j.left
  rw [← pushforward_comp, localTerm, restrict_pushforward_self, integral_pushforward]

end BorelMooreSection

end AlgebraicGeometry.ProEtale.CondensedRing
