/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethBraided
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelHom

/-!

# The statements of Gabber's Künneth formula for nearby cycles

Let `Λ` be a commutative ring object of condensed abelian groups (in practice `𝒪_E`, `𝔽_E` or
`ℚ̄_ℓ`). This file states, for products over the strictly henselian trait `S = Spec k'⟦t⟧` of
models of finite type:

* `NearbyCyclesModel.KunnethFormula Λ k' n`: Gabber's Künneth formula in chart dimension `n`, i.e.
  the Künneth map of nearby cycles `Π_{A,B} : Ψ_M A ⊠ Ψ_N B ⟶ Ψ_P (A ⊠ B)` is an isomorphism for
  bounded constructible `A`, `B` (blueprint `proposition-external-kunneth-formula-nearby-cycles`);
* `NearbyCyclesModel.SliceKunnethFormula Λ k' n`: the generic-slicing step in chart dimension `n`,
  i.e. the pullback of `Π_{A,B}` to the special fibre of the generic slice
  `𝒵 ×_{𝔸¹_S} Spec K⟦t⟧` of the product along a coordinate `b` of the first factor is an
  isomorphism, when the slice of `M` and the total space of `N` locally embed into affine spaces of
  dimensions summing to at most `n` (blueprint `proposition-external-kunneth-formula-nearby-cycles`,
  "Finite support").

It also defines the projections of the geometric slice of a product
(`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`), the models to which the Künneth
formula in smaller chart dimension is applied, and derives the slicing step along a coordinate of
the second factor by symmetry (`NearbyCyclesModel.isIso_map_kunnethMap_baseChangeSpecialMap_snd`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

/-- **Gabber's Künneth formula in chart dimension `n`** over the trait `Spec k'⟦t⟧`, with
coefficients `Λ`: for every product `P` over the trait of models `M`, `N` of finite type, with
projections compatible with the structure morphisms to `Spec Ω`, whose total spaces locally embed
into `𝔸^{m₁}_S` and `𝔸^{m₂}_S` with `m₁ + m₂ ≤ n`, and for bounded constructible `A`, `B`, the
Künneth map of nearby cycles `Π_{A,B}` is an isomorphism. -/
def KunnethFormula (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k' : Type u) [Field k'] (n : ℕ) : Prop :=
  ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
    {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') {qM : M.total ⟶ trait k'}
    {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
    M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
    IsPullback φ₁.total φ₂.total qM qN →
    P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
    φ₂.generic ≫ gN = φ₁.generic ≫ gM → ∀ {m₁ m₂ : ℕ}, m₁ + m₂ ≤ n →
    qM.LocallyEmbedsInAffineSpace m₁ → qN.LocallyEmbedsInAffineSpace m₂ →
    ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
    ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))}
      {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y))},
      boundedConstructible (condensedRingObj Λ X) A →
      boundedConstructible (condensedRingObj Λ Y) B →
      IsIso (kunnethMap Λ φ₁ φ₂ A B)

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
  (hpb : IsPullback φ₁.total φ₂.total qM qN)
  (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
  (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM)

/-! ### The geometric slice of a product along a coordinate of the first factor -/

section Fst

variable {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM)

include hb in
lemma comp_coordinate_fst :
    (φ₁.total ≫ b) ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = φ₁.total ≫ qM := by
  rw [Category.assoc, hb]

/-- The first projection of the geometric slice of a product along a coordinate `b` of the first
factor: the slice of `P` along `φ₁ ≫ b` maps to the slice of `M` along `b`. -/
noncomputable abbrev sliceFst :=
  φ₁.baseChange hM hP hb (traitSlice_over (traitSliceCoord k')) (comp_coordinate_fst hb)
    (traitSlice_over (traitSliceCoord k')) (𝟙 _) (Category.comp_id _) (Category.comp_id _) rfl

include hpb hb in
lemma comp_coordinate_fst_eq :
    (φ₁.total ≫ b) ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = φ₂.total ≫ qN := by
  rw [comp_coordinate_fst hb, hpb.w]

/-- The second projection of the geometric slice of a product along a coordinate `b` of the first
factor: the slice of `P` along `φ₁ ≫ b` maps to the change of trait of `N`. -/
noncomputable abbrev sliceSnd :=
  φ₂.baseChange hN hP (Category.comp_id qN) (Category.comp_id (traitMap k' (traitSliceField k')))
    (comp_coordinate_fst hb) (traitSlice_over (traitSliceCoord k'))
    (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') (comp_coordinate_fst_eq hpb hb)
    (traitSlice_over (traitSliceCoord k')) hgen.symm

end Fst

/-- **The generic-slicing step of Gabber's Künneth formula in chart dimension `n`** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Finite support"), with coefficients `Λ`: for
every product `P` over the trait `Spec k'⟦t⟧` of models `M`, `N` as in
`NearbyCyclesModel.KunnethFormula`, a coordinate `b : 𝒳 ⟶ 𝔸¹_S` of `M` such that the slice of `𝒳`
along `b` and the total space of `N` locally embed into affine spaces of dimensions `m₁`, `m₂` with
`m₁ + m₂ ≤ n`, and bounded constructible `A`, `B`, the pullback of the Künneth map `Π_{A,B}` to the
special fibre of the generic slice `𝒵 ×_{𝔸¹_S} Spec K⟦t⟧` of `P` is an isomorphism.

This is a structure rather than a definition so that the elaborator does not insert the implicit
arguments of the statement when a proof of it is used as a term. -/
structure SliceKunnethFormula (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (k' : Type u) [Field k'] (n : ℕ) : Prop where
  isIso : ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
    {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
    {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
    {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') {qM : M.total ⟶ trait k'}
    {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
    M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
    IsPullback φ₁.total φ₂.total qM qN →
    ∀ (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)),
    φ₂.generic ≫ gN = φ₁.generic ≫ gM → TopologicalSpace.NoetherianSpace X →
    TopologicalSpace.NoetherianSpace Y → TopologicalSpace.NoetherianSpace Z →
    ∀ {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
      (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM) {m₁ m₂ : ℕ}, m₁ + m₂ ≤ n →
    (pullback.snd b (traitSlice (traitSliceCoord k'))).LocallyEmbedsInAffineSpace m₁ →
    qN.LocallyEmbedsInAffineSpace m₂ →
    ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
    ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))}
      {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y))},
      boundedConstructible (condensedRingObj Λ X) A →
      boundedConstructible (condensedRingObj Λ Y) B →
      IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
          (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦Λ⟧).map
        (kunnethMap Λ φ₁ φ₂ A B))

/-! ### Slicing along a coordinate of the second factor -/

section Snd

variable {b : N.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qN)

include hpb hb in
lemma comp_coordinate_snd :
    (φ₂.total ≫ b) ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = φ₁.total ≫ qM := by
  rw [Category.assoc, hb, hpb.w]

-- rewriting the special map of the swapped product in the slice statement is slow
include hM hN hpb hP hgen in
/-- **The generic-slicing step, coordinate of the second factor**: the generic-slicing step
`NearbyCyclesModel.SliceKunnethFormula` for a coordinate `b` of `N`. It is the slicing step for
the product with the two factors exchanged, by the symmetry of the Künneth map
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_swap`). -/
theorem isIso_map_kunnethMap_baseChangeSpecialMap_snd [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] [TopologicalSpace.NoetherianSpace Z]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {n : ℕ} (hslice : SliceKunnethFormula Λ k' n) {m₁ m₂ : ℕ} (hle : m₁ + m₂ ≤ n)
    (h₁ : qM.LocallyEmbedsInAffineSpace m₁)
    (h₂ : (pullback.snd b (traitSlice (traitSliceCoord k'))).LocallyEmbedsInAffineSpace m₂)
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) :
    IsIso (L((baseChangeSpecialMap hP (φ₂.total ≫ b) (comp_coordinate_snd hpb hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦Λ⟧).map
      (kunnethMap Λ φ₁ φ₂ A B)) := by
  have hP' : P.IsTraitModelOver (φ₂.total ≫ qN) (φ₂.generic ≫ gN) := by
    rw [← hpb.w, hgen]
    exact hP
  have h := hslice.isIso φ₂ φ₁ hN hM hpb.flip hP' hgen.symm inferInstance inferInstance
    inferInstance hb (m₁ := m₂) (m₂ := m₁) (by omega)
    h₂ h₁ heN heM hB hA
  have e : baseChangeSpecialMap hP' (φ₂.total ≫ b) (comp_coordinate_fst hb)
      (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')) =
      baseChangeSpecialMap hP (φ₂.total ≫ b) (comp_coordinate_snd hpb hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')) := by
    refine hP.isPullback_i.hom_ext ?_ ?_
    · simp
    · simp [baseChangeSpecialMap]
  have key : ∀ {s s' : (baseChangeSpecial (φ₂.total ≫ b) (traitSlice (traitSliceCoord k'))).left ⟶
      Z'.left}, s = s' → IsIso (L((s)^*⟦Λ⟧).map (kunnethMap Λ φ₂ φ₁ B A)) →
        IsIso (L((s')^*⟦Λ⟧).map (kunnethMap Λ φ₂ φ₁ B A)) := by
    rintro s _ rfl h
    exact h
  have h' := key e (by exact_mod_proofs h)
  exact (isIso_map_kunnethMap_iff_swap _ _ φ₁ φ₂ A B).1 h'

end Snd

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
