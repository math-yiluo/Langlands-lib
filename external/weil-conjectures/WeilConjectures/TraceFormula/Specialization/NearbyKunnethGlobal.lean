/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.OrdinaryKunnethGlobalSections
public import WeilConjectures.TraceFormula.Specialization.TraitProduct
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Gabber's Künneth formula for nearby cycles: global sections

Let `M`, `N` be models of finite type over the henselian trait `S = Spec k'⟦t⟧`
over an arbitrary field `k'` along proper structure morphisms `q_M`, `q_N`, and let `P` be their
product over the trait. This file proves the global-sections step (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, equation (4)) of Illusie's proof of Gabber's
Künneth formula: the direct image `R(a_{P_s})_* Π_{A,B}` of the Künneth map of nearby cycles to the
point `Spec k'` is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_lowerStar_kunnethMap`).
Equivalently, the cone of `Π_{A,B}` has no global sections.

## Proof

After passing to the models of the geometric generic fibres
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_toGeneric`), the structure morphisms are morphisms
of models `ψ : M ⟶ T` to the trait `T` as a model of its geometric generic point
(`NearbyCyclesModel.traitGenericModel`). The compatibility of the Künneth map with direct
images (blueprint `lemma-kunneth-map-proper-direct-image--1`,
`NearbyCyclesModel.kunnethMap_comp_pushforwardExchange`) identifies `R(a_{P_s})_* Π_{A,B}`, up
to
* the proper exchanges `χ_ψ` (blueprint `prose-E-03` (2),
  `NearbyCyclesModel.IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app`),
* the ordinary Künneth isomorphism `RΓ(X_s) ⊗ RΓ(Y_s) ≅ RΓ(X_s × Y_s)` over `k'` (blueprint
  `lemma-kunneth-one-identity-factor--1`,
  `ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback`),

with the Künneth map of the trait `T` at `(RΓ(X_η̄, A), RΓ(Y_η̄, B))` followed by the nearby cycles
of the ordinary Künneth isomorphism on the geometric generic fibres; the former is an isomorphism
because the nearby cycles of the trait are monoidal on bounded constructible complexes on the
geometric generic point; this last input is a hypothesis of
`NearbyCyclesModel.isIso_lowerStar_kunnethMap`, supplied for `ℚ̄_ℓ`-coefficients by
`NearbyCyclesModel.isIso_kunnethMap_traitGenericModel_of_shiftDecomposition`
(`WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal`).

## Implementation notes

The statements of the `ℚ̄_ℓ` inputs carry different `Precoherent Profinite` proofs (auxiliary proof
constants and the synthesized instance) inside the `MonObj` instances of `ℚ̄_ℓ`; comparing them
makes the unifier and the kernel unfold the derived categories. The inputs are therefore applied
with `exact_mod_proofs`, which identifies these proofs by casts.

-/

@[expose] public section


universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### The trait as a model of its geometric generic point -/

section TraitGeneric

variable (k' : Type u) [Field k']

/-- The trait `S = Spec k'⟦t⟧` as a model of its geometric generic point `Spec Ω`, with special
fibre `Spec k'`: the geometric generic point `j : Spec Ω ⟶ S`, the closed point
`i : Spec k' ⟶ S` and `ε = 𝟙`. Its nearby cycles `Ψ_S = i^* Rj_*` are those of SGA 7 XIII, on
complexes on the geometric generic point. -/
noncomputable def traitGenericModel :
    NearbyCyclesModel (Spec (.of (traitGenericField k'))) (Spec (.of k')) where
  total := trait k'
  generic := Spec (.of (traitGenericField k'))
  j := traitGenericPoint k'
  i := traitClosedPoint k'
  ε := 𝟙 _

/-- The trait is a model of finite type over itself as a model of its geometric generic point. -/
theorem isTraitModel_traitGenericModel :
    (traitGenericModel k').IsTraitModel (X' := Over.mk (𝟙 (Spec (.of k')))) := by
  have : IsIso (Over.mk (𝟙 (Spec (.of k')))).hom := inferInstanceAs (IsIso (𝟙 _))
  exact ⟨⟨𝟙 _, 𝟙 _, inferInstance, inferInstance, inferInstance,
    IsPullback.of_vert_isIso ⟨by simp [traitGenericModel]⟩,
    IsPullback.of_vert_isIso ⟨by simp [traitGenericModel]⟩⟩⟩

variable {k'}

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The structure morphisms `q : 𝒳 ⟶ S` and `g : 𝒳_η̄ ⟶ Spec Ω` of a model of finite type over
the trait are a morphism from the model of its geometric generic fibre to the trait. -/
@[simps]
def IsTraitModelOver.toTraitGeneric (h : M.IsTraitModelOver q g) :
    M.toGeneric.Hom (traitGenericModel k') g X'.hom where
  total := q
  generic := g
  comm_j := h.isPullback_j.w.symm
  comm_i := h.isPullback_i.w.symm
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

end TraitGeneric

end NearbyCyclesModel

/-! ### Fibres of a product over the trait -/

section Pasting

variable {C : Type*} [Category C] {Pt Mt Nt S Z X Y s : C} {φ₁ : Pt ⟶ Mt} {φ₂ : Pt ⟶ Nt}
  {qM : Mt ⟶ S} {qN : Nt ⟶ S} {iP : Z ⟶ Pt} {iM : X ⟶ Mt} {iN : Y ⟶ Nt} {hX : X ⟶ s}
  {hY : Y ⟶ s} {hZ : Z ⟶ s} {c : s ⟶ S} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y}

/-- The fibre of a product over a base point: if `P = M ×_S N` and `X`, `Y`, `Z` are the fibres
of `M`, `N`, `P` over `c : s ⟶ S`, the maps `Z ⟶ X`, `Z ⟶ Y` induced by the projections exhibit
`Z` as `X ×_s Y`. -/
lemma isPullback_fibre_of_isPullback (hpb : IsPullback φ₁ φ₂ qM qN)
    (hMi : IsPullback iM hX qM c) (hNi : IsPullback iN hY qN c)
    (hPi : IsPullback iP hZ (φ₁ ≫ qM) c) (c₁ : f₁ ≫ iM = iP ≫ φ₁) (c₂ : f₂ ≫ iN = iP ≫ φ₂)
    (h₁ : f₁ ≫ hX = hZ) (h₂ : f₂ ≫ hY = hZ) : IsPullback f₁ f₂ hX hY := by
  -- the square `Z ⟶ X`, `P ⟶ M` over `iP`, `iM` is cartesian
  have hL : IsPullback f₁ iP iM φ₁ := by
    refine IsPullback.of_right (h₁₂ := hX) (h₂₂ := qM) (v₁₃ := c) ?_ c₁ hMi.flip
    rw [h₁]
    exact hPi.flip
  -- paste it with `P = M ×_S N`
  have hV : IsPullback f₁ (f₂ ≫ iN) (hX ≫ c) qN := by
    rw [c₂, ← hMi.w]
    exact hL.paste_vert hpb
  exact IsPullback.of_bot hV (by rw [h₁, h₂]) hNi.flip

/-- The maps between fibres over a monomorphism `c : s ⟶ S` are maps over `s`. -/
lemma comp_eq_of_mono [Mono c] (hMi : IsPullback iM hX qM c) (hPi : IsPullback iP hZ (φ₁ ≫ qM) c)
    (c₁ : f₁ ≫ iM = iP ≫ φ₁) : f₁ ≫ hX = hZ := by
  rw [← cancel_mono c, Category.assoc, ← hMi.w, reassoc_of% c₁, hPi.w]

end Pasting

namespace NearbyCyclesModel

section Product

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

instance : IsClosedImmersion (traitClosedPoint k') :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩

/-- The morphism of special fibres of the first projection of a product over the trait lies over
`Spec k'`. -/
lemma special_comp_hom_fst (hM : M.IsTraitModelOver qM gM)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) : f₁' ≫ X'.hom = Z'.hom :=
  comp_eq_of_mono hM.isPullback_i hP.isPullback_i φ₁.comm_i

/-- The morphism of special fibres of the second projection of a product over the trait lies over
`Spec k'`. -/
lemma special_comp_hom_snd (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) : f₂' ≫ Y'.hom = Z'.hom := by
  rw [hpb.w] at hP
  exact comp_eq_of_mono hN.isPullback_i hP.isPullback_i φ₂.comm_i

/-- The special fibre of a product over the trait is the product of the special fibres. -/
lemma isPullback_special (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) :
    IsPullback f₁' f₂' X'.hom Y'.hom :=
  isPullback_fibre_of_isPullback hpb hM.isPullback_i hN.isPullback_i hP.isPullback_i φ₁.comm_i
    φ₂.comm_i (special_comp_hom_fst hM hP) (special_comp_hom_snd hN hpb hP)

/-- The geometric generic fibre of a product over the trait is the product of the geometric
generic fibres over `Spec Ω`, if the projections are compatible with the structure morphisms to
`Spec Ω`. -/
lemma isPullback_generic (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) :
    IsPullback φ₁.generic φ₂.generic gM gN :=
  isPullback_fibre_of_isPullback hpb hM.isPullback_j hN.isPullback_j hP.isPullback_j φ₁.comm_j
    φ₂.comm_j rfl hgen

end Product

/-! ### The proper exchange and the nearby cycles of the trait -/

section Exchange

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [Fact (ringChar k' ≠ ℓ)] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

-- the pushforward exchange of the model of the geometric generic fibre is slow to unify
/-- **The proper exchange for the structure morphism** (blueprint
`prose-E-03` (2), for the proper morphism `f = q : 𝒳 ⟶ S` to the trait; SGA 7
XIII (2.1.7.1)): for a model `M` of finite type over the henselian trait `Spec k'⟦t⟧` along a
proper `q` and a bounded constructible complex `C₀` on the total space, the pushforward exchange
`χ : Ψ_S Rg_* (Lj^* C₀) ⟶ R(q_s)_* Ψ_M (Lj^* C₀)` of the structure morphism
`(q, g) : M ⟶ S` (`NearbyCyclesModel.IsTraitModelOver.toTraitGeneric`) is an isomorphism. Here
`Lj^* C₀` is the pullback to the geometric generic fibre of the complex `C₀|_{𝒳_η}` on the
generic fibre, as in the blueprint node, and `Ψ_S Rg_*` is the nearby cycles of the trait of
`Rq_{η*}`, computed on the geometric generic fibre.

This is the node for the morphism `(q, g)` from the model of the geometric generic fibre to the
trait as a model of its geometric generic point. The version for geometric models
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`) is the same
statement for `(q, q) : M.geometric ⟶ S.geometric`; the two exchanges differ by `Ψ_S` of the
base change morphism `Lη̄^* Rq_* ⟶ Rg_* Lj^*`, which is invertible by proper base change for
`q`. -/
theorem IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app
    (h : M.IsTraitModelOver q g) [IsProper q]
    (C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)))
    (hC₀ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) C₀) :
    IsIso ((h.toTraitGeneric.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app
        (L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C₀)) := by
  have : IsProper h.toTraitGeneric.total := ‹IsProper q›
  have : IsProper g := MorphismProperty.of_isPullback h.isPullback_j ‹IsProper q›
  have : IsIso (traitGenericModel k').ε :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of (traitGenericField k')))))
  exact h.toTraitGeneric.isIso_pushforwardExchange_app_of_isProper
    (traitGenericPoint k' ≫ traitToBase k' k') ⟨_, ⟨h.isTraitModel.exists_isPullback⟩⟩
    ⟨𝟙 _, isTraitModel_traitGenericModel k'⟩
    h.isPullback_i (IsPullback.of_horiz_isIso ⟨rfl⟩)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.j C₀ hC₀)

end Exchange

/-- A natural transformation is invertible at an object isomorphic to one where it is
invertible. -/
lemma _root_.CategoryTheory.NatTrans.isIso_app_of_iso' {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (τ : F ⟶ G) {U U' : C} (e : U ≅ U') [IsIso (τ.app U')] : IsIso (τ.app U) := by
  have h : τ.app U = F.map e.hom ≫ τ.app U' ≫ G.map e.inv := by
    rw [τ.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [h]
  infer_instance

/-! ### Transport along pullbacks, for general coefficients -/

section Transport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Pullbacks along the two sides of a commutative square are isomorphic. -/
lemma nonempty_upperStar_obj_iso_of_comm {W T T' V : Scheme.{u}} {a : W ⟶ T} {b : T ⟶ V}
    {c : W ⟶ T'} {d : T' ⟶ V} (w : a ≫ b = c ≫ d)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :
    Nonempty (L((a)^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj A) ≅ L((c)^*⟦Λ⟧).obj (L((d)^*⟦Λ⟧).obj A)) :=
  ⟨(pullbackSquareComparison Λ (⟨w.symm⟩ : CommSq c a d b)).app A⟩

/-- The pullback along a composite is the composite of the pullbacks. -/
lemma nonempty_upperStar_obj_iso_comp {W T V : Scheme.{u}} {a : W ⟶ T} {b : T ⟶ V} {c : W ⟶ V}
    (w : a ≫ b = c)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :
    Nonempty (L((c)^*⟦Λ⟧).obj A ≅ L((a)^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj A)) := by
  subst w
  exact ⟨(leftDerivedUpperStarComp Λ a b).app A⟩

variable {X Y Z X' Y' Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

-- the monoidal structure of the derived categories of module objects is slow to unify
/-- If the identifications `ε` of `M` and `N` factor through the total spaces, the external
product `Lφ₁^* Lε_M^* A ⊗ Lφ₂^* Lε_N^* B` on the geometric generic fibre of `P` is the pullback
`Lj_P^* C₀` of a bounded constructible complex `C₀` on the total space of `P`, provided bounded
constructible complexes on the total space of `P` are stable under `⊗`. -/
lemma exists_boundedConstructible_tensor_iso (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B)
    (htensor : ∀ C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P.total) Ab.{u + 1})
        (condensedRingObj Λ P.total)),
      boundedConstructible (condensedRingObj Λ P.total) C →
        boundedConstructible (condensedRingObj Λ P.total) D →
          boundedConstructible (condensedRingObj Λ P.total) (C ⊗ D)) :
    ∃ C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P.total) Ab.{u + 1})
        (condensedRingObj Λ P.total)),
      boundedConstructible (condensedRingObj Λ P.total) C₀ ∧
        Nonempty (L((φ₁.generic)^*⟦Λ⟧).obj (L((M.ε)^*⟦Λ⟧).obj A) ⊗
          L((φ₂.generic)^*⟦Λ⟧).obj (L((N.ε)^*⟦Λ⟧).obj B) ≅ L((P.j)^*⟦Λ⟧).obj C₀) := by
  have w₁ : φ₁.generic ≫ M.ε = P.j ≫ φ₁.total ≫ eM := by
    rw [← heM, ← Category.assoc, φ₁.comm_j, Category.assoc]
  have w₂ : φ₂.generic ≫ N.ε = P.j ≫ φ₂.total ≫ eN := by
    rw [← heN, ← Category.assoc, φ₂.comm_j, Category.assoc]
  exact ⟨_, htensor _ _ (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ A hA)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ B hB),
    ⟨((nonempty_upperStar_obj_iso_of_comm Λ w₁ A).some ⊗ᵢ
      (nonempty_upperStar_obj_iso_of_comm Λ w₂ B).some) ≪≫
      Functor.Monoidal.μIso L((P.j)^*⟦Λ⟧) _ _⟩⟩

/-- A natural transformation invertible at all pullbacks `Lj^* C₀` of bounded constructible
complexes `C₀` on the total space of a model is invertible at every complex isomorphic to one. -/
lemma isIso_app_of_forall_upperStar {X'' : Scheme.{u}} {M : NearbyCyclesModel X X''}
    {C : Type*} [Category C]
    {F G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ M.generic)) ⥤ C} (τ : F ⟶ G)
    (hτ : ∀ C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
        (condensedRingObj Λ M.total)), boundedConstructible (condensedRingObj Λ M.total) C₀ →
      IsIso (τ.app (L((M.j)^*⟦Λ⟧).obj C₀)))
    (U : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ M.generic)))
    (hU : ∃ C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
        (condensedRingObj Λ M.total)), boundedConstructible (condensedRingObj Λ M.total) C₀ ∧
      Nonempty (U ≅ L((M.j)^*⟦Λ⟧).obj C₀)) :
    IsIso (τ.app U) := by
  obtain ⟨C₀, hC₀, ⟨e⟩⟩ := hU
  have := hτ C₀ hC₀
  exact NatTrans.isIso_app_of_iso' τ e

/-- Passing to the geometric generic model preserves bounded constructibility of nearby
cycles. -/
private lemma boundedConstructible_nearbyCycles_toGeneric
    (M : NearbyCyclesModel X X')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hA : boundedConstructible (condensedRingObj Λ X') ((M.nearbyCycles Λ).obj A)) :
    boundedConstructible (condensedRingObj Λ X')
      ((M.toGeneric.nearbyCycles Λ).obj (L((M.ε)^*⟦Λ⟧).obj A)) :=
  (boundedConstructible _).prop_of_iso (L((M.i)^*⟦Λ⟧).mapIso
    (R((M.j)_*⟦Λ⟧).mapIso ((leftDerivedUpperStarId _ M.generic).app _))).symm hA

end Transport

/-- The proper exchange is invertible at any complex isomorphic to the pullback of a bounded
constructible complex on the total space. -/
private lemma IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_of_iso
    {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [Fact (ringChar k' ≠ ℓ)]
    {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOver q g) [IsProper q]
    (U : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)))
    (hU : ∃ C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) C₀ ∧
        Nonempty (U ≅ L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C₀)) :
    IsIso ((h.toTraitGeneric.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app U) := by
  obtain ⟨C₀, hC₀, ⟨e⟩⟩ := hU
  have : IsIso ((h.toTraitGeneric.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app
      (L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C₀)) := by
    exact_mod_proofs h.isIso_pushforwardExchange_toTraitGeneric_app (ℓ := ℓ) C₀ hC₀
  exact NatTrans.isIso_app_of_iso' _ e

/-! ### The global-sections step, for general coefficients -/

section GlobalAbstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- If `a ≫ b ≫ c = d ≫ e ≫ f` with `a`, `b`, `d`, `e`, `f` invertible, then `c` is invertible. -/
lemma isIso_of_square {C : Type*} [Category C] {W X₁ X₂ X₃ Y₁ Y₂ : C} {a : W ⟶ X₁}
    {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : W ⟶ Y₁} {e : Y₁ ⟶ Y₂} {f : Y₂ ⟶ X₃}
    (h : a ≫ b ≫ c = d ≫ e ≫ f) (ha : IsIso a) (hb : IsIso b) (hd : IsIso d) (he : IsIso e)
    (hf : IsIso f) : IsIso c := by
  have : IsIso (a ≫ b ≫ c) := h ▸ inferInstance
  have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a _
  exact IsIso.of_isIso_comp_left b c

set_option maxHeartbeats 1600000 in
-- the composite square identifying the direct image of the Künneth map has large terms
/-- **The global-sections step, abstractly**: for the product `P` over the trait of models `M`,
`N` of finite type, with projections compatible with the structure morphisms to `Spec Ω`, the
direct image `R(a_{P_s})_* Π_{A,B}` of the Künneth map to the point `Spec k'` is an isomorphism
as soon as the proper exchanges `χ` of the structure morphisms to the trait, the ordinary Künneth
maps on the special and on the geometric generic fibres, and the Künneth map of the trait at
`(Rg_{M*} Lε_M^* A, Rg_{N*} Lε_N^* B)` are isomorphisms (the identification
`kunnethMap_comp_pushforwardExchange` of blueprint `lemma-kunneth-map-proper-direct-image--1`). -/
theorem isIso_lowerStar_kunnethMap_of_isIso (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hχM : IsIso ((hM.toTraitGeneric.pushforwardExchange Λ).app (L((M.ε)^*⟦Λ⟧).obj A)))
    (hχN : IsIso ((hN.toTraitGeneric.pushforwardExchange Λ).app (L((N.ε)^*⟦Λ⟧).obj B)))
    (hχP : IsIso ((hP.toTraitGeneric.pushforwardExchange Λ).app
      (L((φ₁.generic)^*⟦Λ⟧).obj (L((M.ε)^*⟦Λ⟧).obj A) ⊗
        L((φ₂.generic)^*⟦Λ⟧).obj (L((N.ε)^*⟦Λ⟧).obj B))))
    (hκs : IsIso (lowerStarKunnethMap' Λ
      (⟨(special_comp_hom_fst hM hP).trans (Category.comp_id _).symm⟩ :
        CommSq f₁' Z'.hom X'.hom (𝟙 _))
      (⟨(special_comp_hom_snd hN hpb hP).trans (Category.comp_id _).symm⟩ :
        CommSq f₂' Z'.hom Y'.hom (𝟙 _))
      ((M.toGeneric.nearbyCycles Λ).obj (L((M.ε)^*⟦Λ⟧).obj A))
      ((N.toGeneric.nearbyCycles Λ).obj (L((N.ε)^*⟦Λ⟧).obj B))))
    (hκΩ : IsIso (lowerStarKunnethMap' Λ
      (⟨(Category.comp_id _).symm⟩ : CommSq φ₁.generic (φ₁.generic ≫ gM) gM (𝟙 _))
      (⟨hgen.trans (Category.comp_id _).symm⟩ : CommSq φ₂.generic (φ₁.generic ≫ gM) gN (𝟙 _))
      (L((M.ε)^*⟦Λ⟧).obj A) (L((N.ε)^*⟦Λ⟧).obj B)))
    (hT : IsIso (kunnethMap Λ (Hom.id (traitGenericModel k')) (Hom.id (traitGenericModel k'))
      (R((gM)_*⟦Λ⟧).obj (L((M.ε)^*⟦Λ⟧).obj A)) (R((gN)_*⟦Λ⟧).obj (L((N.ε)^*⟦Λ⟧).obj B)))) :
    IsIso (R((Z'.hom)_*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) := by
  refine (isIso_map_kunnethMap_iff_toGeneric _ φ₁ φ₂ A B _).2 ?_
  have sq := kunnethMap_comp_pushforwardExchange Λ
    φ₁.toGeneric φ₂.toGeneric (Hom.id (traitGenericModel k')) (Hom.id (traitGenericModel k'))
    hM.toTraitGeneric hN.toTraitGeneric hP.toTraitGeneric (Category.comp_id _).symm
    (Category.comp_id _).symm ((Category.comp_id _).trans hpb.w).symm
    (hgen.trans (Category.comp_id _).symm) (Category.comp_id _).symm
    ((special_comp_hom_fst hM hP).trans (Category.comp_id _).symm)
    (hgen.trans (Category.comp_id _).symm)
    ((special_comp_hom_snd hN hpb hP).trans (Category.comp_id _).symm)
    (L((M.ε)^*⟦Λ⟧).obj A) (L((N.ε)^*⟦Λ⟧).obj B)
  exact isIso_of_square sq inferInstance hκs hT (Functor.map_isIso _ _) hχP

end GlobalAbstract

/-! ### The global-sections step -/

section TraitGenericField

variable (ℓ : ℕ) {k' : Type u} [Field k']

/-- The geometric generic point of the trait has the characteristic of `k'`. -/
lemma ringChar_traitGenericField : ringChar (traitGenericField k') = ringChar k' :=
  (Algebra.ringChar_eq k' _).symm

instance [Fact (ringChar k').Prime] : Fact (ringChar (traitGenericField k')).Prime :=
  ⟨by rw [ringChar_traitGenericField]; exact Fact.out⟩

instance [Fact (ringChar k' ≠ ℓ)] : Fact (ringChar (traitGenericField k') ≠ ℓ) :=
  ⟨by rw [ringChar_traitGenericField]; exact Fact.out⟩

end TraitGenericField

section Global

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- Bounded constructible complexes on the total space of a trait model are closed under
tensor products. -/
private lemma IsTraitModelOver.boundedConstructible_tensor_total
    {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOver q g)
    (C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) C)
    (hD : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) D) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) (C ⊗ D) := by
  have := h.locallyOfFiniteType
  have := h.quasiCompact
  have : IsLocallyNoetherian M.total := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace M.total := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian M.total := {}
  exact boundedConstructible_tensorObj
    (tensorHypotheses_padicAlgClRingObj ℓ).lisseTensorHypotheses hC hD

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

-- the composite square identifying the direct image of the Künneth map has large terms
/-- **The global-sections step of Gabber's Künneth formula** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, equation (4); Illusie, *Autour du théorème de
monodromie locale*, proof of Thm. 4.7): let `P` be the product over the henselian trait `Spec k'⟦t⟧`
of models `M`, `N` of finite type along proper structure morphisms `q_M`, `q_N`, whose projections
are compatible with the structure morphisms `g` of the geometric generic fibres to `Spec Ω`. For
bounded constructible `A`, `B` (whose nearby cycles are bounded constructible, Deligne's
finiteness theorem), the direct image `R(a_{P_s})_* Π_{A,B}` of the Künneth map of nearby cycles
to the point `Spec k'` is an isomorphism: under the proper exchanges and the ordinary Künneth
formula on the special fibres, it is the Künneth isomorphism
`RΓ(X_η̄, A) ⊗ RΓ(Y_η̄, B) ≅ RΓ(X_η̄ × Y_η̄, A ⊠ B)` of the geometric generic fibres. -/
theorem isIso_lowerStar_kunnethMap (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B)
    (hΨA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj A))
    (hΨB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left)
      ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj B))
    (hT : IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (Hom.id (traitGenericModel k')) (Hom.id
        (traitGenericModel k'))
      (R((gM)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          A)) (R((gN)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (L((N.ε)^*⟦Profinite.padicAlgClRingObj
              ℓ⟧).obj B)))) :
    IsIso (R((Z'.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  -- the structure morphisms and their properties
  have hqP : IsProper (φ₁.total ≫ qM) := by
    have : IsProper φ₁.total := MorphismProperty.of_isPullback hpb.flip inferInstance
    infer_instance
  have hs₁ := special_comp_hom_fst hM hP
  have hs₂ := special_comp_hom_snd hN hpb hP
  have : LocallyOfFiniteType X'.hom := MorphismProperty.of_isPullback hM.isPullback_i
    hM.locallyOfFiniteType
  have : QuasiCompact X'.hom := MorphismProperty.of_isPullback hM.isPullback_i
    hM.quasiCompact
  have : IsSeparated X'.hom := MorphismProperty.of_isPullback hM.isPullback_i
    hM.isSeparated
  have : LocallyOfFiniteType Y'.hom := MorphismProperty.of_isPullback hN.isPullback_i
    hN.locallyOfFiniteType
  have : QuasiCompact Y'.hom := MorphismProperty.of_isPullback hN.isPullback_i
    hN.quasiCompact
  have : IsSeparated Y'.hom := MorphismProperty.of_isPullback hN.isPullback_i
    hN.isSeparated
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : QuasiCompact Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.quasiCompact
  have : IsSeparated Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.isSeparated
  have : LocallyOfFiniteType (Over.mk gM).hom := MorphismProperty.of_isPullback
    hM.isPullback_j hM.locallyOfFiniteType
  have : QuasiCompact (Over.mk gM).hom := MorphismProperty.of_isPullback hM.isPullback_j
    hM.quasiCompact
  have : IsSeparated (Over.mk gM).hom := MorphismProperty.of_isPullback hM.isPullback_j
    hM.isSeparated
  have : LocallyOfFiniteType (Over.mk gN).hom := MorphismProperty.of_isPullback
    hN.isPullback_j hN.locallyOfFiniteType
  have : QuasiCompact (Over.mk gN).hom := MorphismProperty.of_isPullback hN.isPullback_j
    hN.quasiCompact
  have : IsSeparated (Over.mk gN).hom := MorphismProperty.of_isPullback hN.isPullback_j
    hN.isSeparated
  have : LocallyOfFiniteType (Over.mk (φ₁.generic ≫ gM)).hom := MorphismProperty.of_isPullback
    hP.isPullback_j hP.locallyOfFiniteType
  have : QuasiCompact (Over.mk (φ₁.generic ≫ gM)).hom := MorphismProperty.of_isPullback
    hP.isPullback_j hP.quasiCompact
  have : IsSeparated (Over.mk (φ₁.generic ≫ gM)).hom := MorphismProperty.of_isPullback
    hP.isPullback_j hP.isSeparated
  -- the complexes on the geometric generic fibres
  have hA' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A hA
  have hB' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ N.ε B hB
  have hΨA' := boundedConstructible_nearbyCycles_toGeneric _ M A hΨA
  have hΨB' := boundedConstructible_nearbyCycles_toGeneric _ N B hΨB
  have htensor := hP.boundedConstructible_tensor_total (ℓ := ℓ)
  refine isIso_lowerStar_kunnethMap_of_isIso (Profinite.padicAlgClRingObj ℓ) hM hN hpb hP
    hgen A B ?_ ?_ ?_ ?_ ?_ hT
  -- Transport each proper exchange directly along its pullback isomorphism.
  · have hχ := hM.isIso_pushforwardExchange_toTraitGeneric_of_iso (ℓ := ℓ) _
      ⟨_, boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ eM A hA,
        nonempty_upperStar_obj_iso_comp _ heM A⟩
    exact_mod_proofs hχ
  · have hχ := hN.isIso_pushforwardExchange_toTraitGeneric_of_iso (ℓ := ℓ) _
      ⟨_, boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ eN B hB,
        nonempty_upperStar_obj_iso_comp _ heN B⟩
    exact_mod_proofs hχ
  · have hχ := hP.isIso_pushforwardExchange_toTraitGeneric_of_iso (ℓ := ℓ) _
      (exists_boundedConstructible_tensor_iso _ φ₁ φ₂ heM heN hA hB htensor)
    exact_mod_proofs hχ
  -- the ordinary Künneth formulas on the special fibres and on the geometric generic fibres
  · exact_mod_proofs isIso_lowerStarKunnethMap'_of_isPullback (ℓ := ℓ)
      (X := X') (Y := Y') (P := Z') f₁' f₂'
      (hs₁.trans (Category.comp_id _).symm) (hs₂.trans (Category.comp_id _).symm)
      (isPullback_special hM hN hpb hP) _ hΨA' _ hΨB'
  · exact_mod_proofs isIso_lowerStarKunnethMap'_of_isPullback (ℓ := ℓ)
      (K := traitGenericField k') (X := Over.mk gM)
      (Y := Over.mk gN)
      (P := Over.mk (φ₁.generic ≫ gM)) φ₁.generic φ₂.generic (Category.comp_id _).symm
      (hgen.trans (Category.comp_id _).symm) (isPullback_generic hM hN hpb hP hgen) _ hA' _ hB'

end Global

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
