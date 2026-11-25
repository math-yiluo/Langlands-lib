/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationTraceSpecialization
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityExchange
public import WeilConjectures.Tactic.MatchTactic
public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProper
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback

/-!

# Nearby cycles of the universal kernel, abstractly

Let `S_X`, `S_{X×X}` be nearby cycles on `X` and `X ×_S X`, `Δ` the diagonal, `K` a complex on the
generic fibre and `K' = S_X K`. With the external product comparison
`Π : K' ⊠ S_X D K ⟶ S_{X×X}(K ⊠ D K)` and the duality map `δ_K : S_X D K ⟶ D K'` invertible, put
`ρ = (1 ⊠ δ_K) ∘ Π⁻¹ : S_{X×X}(K ⊠ D K) ⟶ K' ⊠ D K'`. The second identity of blueprint
`lemma-nearby-cycles-universal-kernel` is

`e_{K'} ∘ ρ = RΔ_{s*} θ_X ∘ χ_Δ ∘ S(e_K)`,

for the evaluation kernels `e_K : K ⊠ D K ⟶ RΔ_* ω_X`, and the first one is

`𝔥 S(λ_K) = λ_{K'} ρ`,

for the external-duality maps `λ_K : K ⊠ D K ⟶ RHom(p_2^* K, p_1^! K)` and the exchange
`𝔥 : S RHom(p_2^* K, p_1^! K) ⟶ RHom(p_{2s}^* K', p_{1s}^! K')`. This file proves both for
abstract adjunctions and monoidal closed categories:

* `CategoryTheory.comp_homEquiv_eq_map_homEquiv_comp_exchange`: both sides are the adjoints of
  the same map, given the mate property of `χ_Δ` and the restriction of `ρ` to the diagonal;
* `CategoryTheory.map_comp_ev_eq_of_kunneth`: the restriction of `ρ` to the diagonal is the
  pairing `θ ∘ S(ev) ∘ μ` defining `δ_K`, given that `Δ_s^* Π` is the lax tensor map `μ_X` (the
  composition law and monoidality of the pullback exchanges, with `p_i ∘ Δ = 1`);
* `CategoryTheory.map_curry_kunnethPairing_comp_eq`: the first identity, given the definition of
  `δ_K`, the monoidality of `α_{p_2}`, the compatibility of the exceptional Künneth map with the
  exchanges and the symmetry of the lax tensor maps. It reduces to the adjoint pairings
  (`CategoryTheory.map_comp_eq_comp_of_pairing`), which agree by
  `CategoryTheory.pairing_specialization_eq`.

It also defines `ρ` for the specialization to the normal cone
(`ProEtale.CondensedRing.universalKernelSpecialization`) and proves the ambient form of
`Δ_s^* Π = μ_X`
(`ProEtale.CondensedRing.NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction`);
the second identity for the specialization is in
`WeilConjectures.TraceFormula.Specialization.UniversalKernelDiagonal`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {CP CX CP' CX' : Type*} [Category CP] [Category CX] [Category CP'] [Category CX']

/-- **The evaluation kernel identity**, abstractly: for adjunctions `U ⊣ R` (`Δ_η^* ⊣ RΔ_{η*}`)
and `U' ⊣ R'`, a transformation `α : S_P ⋙ U' ⟶ U ⋙ S_X` and its mate `χ : R ⋙ S_P ⟶ S_X ⋙ R'`,
if the restriction of `ρ : S_P P ⟶ P'` along `U'` composed with `ev'` is `α ≫ S_X(ev) ≫ θ`, then
`ρ` followed by the adjoint of `ev'` is `S_P` of the adjoint of `ev` followed by `χ` and
`R'(θ)`. -/
theorem comp_homEquiv_eq_map_homEquiv_comp_exchange {U : CP ⥤ CX} {R : CX ⥤ CP} (a : U ⊣ R)
    {U' : CP' ⥤ CX'} {R' : CX' ⥤ CP'} (a' : U' ⊣ R') {SP : CP ⥤ CP'} {SX : CX ⥤ CX'}
    (α : SP ⋙ U' ⟶ U ⋙ SX) (χ : R ⋙ SP ⟶ SX ⋙ R')
    (hχ : ∀ A, U'.map (χ.app A) ≫ a'.counit.app _ = α.app (R.obj A) ≫ SX.map (a.counit.app A))
    {P : CP} {P' : CP'} {ω : CX} {ω' : CX'} (ev : U.obj P ⟶ ω) (ev' : U'.obj P' ⟶ ω')
    (θ : SX.obj ω ⟶ ω') (ρ : SP.obj P ⟶ P')
    (hρ : U'.map ρ ≫ ev' = α.app P ≫ SX.map ev ≫ θ) :
    ρ ≫ a'.homEquiv _ _ ev' = SP.map (a.homEquiv _ _ ev) ≫ χ.app ω ≫ R'.map θ := by
  apply (a'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, hρ,
    Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, Adjunction.counit_naturality, ← Category.assoc (U'.map (χ.app ω)),
    hχ]
  have hn := α.naturality (a.homEquiv _ _ ev)
  simp only [Functor.comp_map] at hn
  have he : U.map (a.homEquiv _ _ ev) ≫ a.counit.app ω = ev := by
    simp [Adjunction.homEquiv_unit]
  rw [Category.assoc, reassoc_of% hn, ← SX.map_comp_assoc, he]

/-- The cancellation of the identity isomorphisms `I : E ≅ 𝟭`, `I' : F ≅ 𝟭` around
`a = I'(Ψ C) ≫ Ψ(I⁻¹ C)` and `b = I'(Ψ E C) ≫ Ψ(I⁻¹(E C))` (the pullback exchanges of identity
morphisms of models). -/
lemma map_comp_comp_map_of_isoId {C D : Type*} [Category C] [Category D] (Ψ : C ⥤ D) {F : D ⥤ D}
    (I' : F ≅ 𝟭 D) {E : C ⥤ C} (I : E ≅ 𝟭 C) (C₀ : C) {a : F.obj (Ψ.obj C₀) ⟶ Ψ.obj (E.obj C₀)}
    {b : F.obj (Ψ.obj (E.obj C₀)) ⟶ Ψ.obj (E.obj (E.obj C₀))}
    (ha : a = I'.hom.app (Ψ.obj C₀) ≫ Ψ.map (I.inv.app C₀))
    (hb : b = I'.hom.app (Ψ.obj (E.obj C₀)) ≫ Ψ.map (I.inv.app (E.obj C₀))) :
    F.map a ≫ b ≫ Ψ.map (I.hom.app (E.obj C₀) ≫ I.hom.app C₀) =
      I'.hom.app (F.obj (Ψ.obj C₀)) ≫ I'.hom.app (Ψ.obj C₀) := by
  subst ha hb
  have hn := I'.hom.naturality (I'.hom.app (Ψ.obj C₀) ≫ Ψ.map (I.inv.app C₀))
  simp only [Functor.id_map, Functor.id_obj] at hn
  rw [Category.assoc, reassoc_of% hn]
  simp only [← Ψ.map_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Functor.id_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The algebra of `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction`: from
the compatibility `h` of the Künneth map with pullbacks along the identity morphisms of models,
the naturality of the lax tensor maps and the cancellations `hcA`, `hcB` of the identity
isomorphisms. -/
lemma kunneth_retraction_aux {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (Ψ : C ⥤ D) {S X₁ eA eB fA fB gA gB hA hB : D}
    {c₀ cA cB A₂ B₂ A₁ B₁ A B : C} (P₁ : S ⟶ X₁) (P₂ : X₁ ⟶ Ψ.obj c₀) (δ : c₀ ⟶ cA ⊗ cB)
    (θA : cA ⟶ A₂) (θB : cB ⟶ B₂) (iA₁ : A₂ ⟶ A₁) (iA : A₁ ⟶ A) (iB₁ : B₂ ⟶ B₁) (iB : B₁ ⟶ B)
    (δ' : S ⟶ eA ⊗ eB) (θ'A : eA ⟶ fA) (θ'B : eB ⟶ fB) (La : fA ⟶ gA) (Lb : fB ⟶ gB)
    (a₁ : gA ⟶ Ψ.obj A₂) (b₁ : gB ⟶ Ψ.obj B₂) (μ₁ : Ψ.obj A₂ ⊗ Ψ.obj B₂ ⟶ Ψ.obj (A₂ ⊗ B₂))
    (μ : Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B))
    (hnat : (Ψ.map (iA₁ ≫ iA) ⊗ₘ Ψ.map (iB₁ ≫ iB)) ≫ μ = μ₁ ≫ Ψ.map ((iA₁ ≫ iA) ⊗ₘ (iB₁ ≫ iB)))
    (jA₁ : fA ⟶ hA) (jA : hA ⟶ Ψ.obj A) (jB₁ : fB ⟶ hB) (jB : hB ⟶ Ψ.obj B)
    (hcA : La ≫ a₁ ≫ Ψ.map (iA₁ ≫ iA) = jA₁ ≫ jA) (hcB : Lb ≫ b₁ ≫ Ψ.map (iB₁ ≫ iB) = jB₁ ≫ jB)
    (h : P₁ ≫ P₂ ≫ Ψ.map (δ ≫ (θA ⊗ₘ θB)) =
      δ' ≫ ((θ'A ≫ La) ⊗ₘ (θ'B ≫ Lb)) ≫ (a₁ ⊗ₘ b₁) ≫ μ₁)
    {mA : C} {mB : C} {mA' mB' : D} {gA₁ : cA ⟶ mA} {gA₂ : mA ⟶ A₁} {gB₁ : cB ⟶ mB}
    {gB₂ : mB ⟶ B₁} {g'A₁ : eA ⟶ mA'} {g'A₂ : mA' ⟶ hA} {g'B₁ : eB ⟶ mB'}
    {g'B₂ : mB' ⟶ hB}
    (ecA : θA ≫ iA₁ = gA₁ ≫ gA₂) (ecB : θB ≫ iB₁ = gB₁ ≫ gB₂)
    (ec'A : θ'A ≫ jA₁ = g'A₁ ≫ g'A₂) (ec'B : θ'B ≫ jB₁ = g'B₁ ≫ g'B₂) :
    P₁ ≫ P₂ ≫ Ψ.map (δ ≫ ((gA₁ ≫ gA₂ ≫ iA) ⊗ₘ (gB₁ ≫ gB₂ ≫ iB))) =
      δ' ≫ ((g'A₁ ≫ g'A₂ ≫ jA) ⊗ₘ (g'B₁ ≫ g'B₂ ≫ jB)) ≫ μ := by
  simp only [← Category.assoc gA₁, ← Category.assoc gB₁, ← Category.assoc g'A₁,
    ← Category.assoc g'B₁, ← ecA, ← ecB, ← ec'A, ← ec'B]
  have e : δ ≫ (((θA ≫ iA₁) ≫ iA) ⊗ₘ ((θB ≫ iB₁) ≫ iB)) =
      (δ ≫ (θA ⊗ₘ θB)) ≫ ((iA₁ ≫ iA) ⊗ₘ (iB₁ ≫ iB)) := by
    simp only [Category.assoc, tensorHom_comp_tensorHom]
  rw [e, Ψ.map_comp, reassoc_of% h, ← hnat]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, hcA, hcB]

/-- Naturality of `(α_ _ _ _).inv ≫ (β ▷ _) ≫ (α_ _ _ _).hom : A ⊗ (B ⊗ C) ⟶ B ⊗ (A ⊗ C)`. -/
@[reassoc]
theorem whiskerRight_whiskerLeft_braiding_comp {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {A A' B B' Z Z' E : C} (a : A' ⟶ A) (b : B' ⟶ B) (c : Z' ⟶ Z)
    (f : A ⊗ Z ⟶ E) :
    a ▷ (B' ⊗ Z') ≫ A ◁ (b ⊗ₘ c) ≫ (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        B ◁ f =
      (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫ (b ⊗ₘ ((a ⊗ₘ c) ≫ f)) := by
  rw [← tensorHom_def_assoc, associator_inv_naturality_assoc, ← tensorHom_id, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, BraidedCategory.braiding_naturality, Category.comp_id,
    ← Category.id_comp c, ← tensorHom_comp_tensorHom_assoc, associator_naturality_assoc,
    Category.id_comp, tensorHom_id, tensorHom_comp_whiskerLeft]

/-- For a lax monoidal functor `F` compatible with the braidings, the lax tensor maps
`F X ⊗ (F Y ⊗ F Z) ⟶ F (X ⊗ (Y ⊗ Z))` commute with the exchange of the first two factors
`(α_ _ _ _).inv ≫ (β ▷ _) ≫ (α_ _ _ _).hom`. -/
theorem Functor.LaxMonoidal.μ_comp_map_braiding_exchange {CP CP' : Type*}
    [Category CP] [Category CP']
    [MonoidalCategory CP] [MonoidalCategory CP'] [BraidedCategory CP] [BraidedCategory CP']
    {SP : CP ⥤ CP'} [SP.LaxMonoidal]
    (hbr : ∀ X Y : CP, Functor.LaxMonoidal.μ SP X Y ≫ SP.map (β_ X Y).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ SP Y X) (X Y Z : CP) :
    SP.obj X ◁ Functor.LaxMonoidal.μ SP Y Z ≫ Functor.LaxMonoidal.μ SP X (Y ⊗ Z) ≫
        SP.map ((α_ _ _ _).inv ≫ ((β_ X Y).hom ▷ Z) ≫ (α_ _ _ _).hom) =
      (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        SP.obj Y ◁ Functor.LaxMonoidal.μ SP X Z ≫ Functor.LaxMonoidal.μ SP Y (X ⊗ Z) := by
  have h1 := Functor.LaxMonoidal.associativity SP X Y Z
  have h2 := Functor.LaxMonoidal.associativity SP Y X Z
  rw [← cancel_epi (α_ (SP.obj X) (SP.obj Y) (SP.obj Z)).hom, ← reassoc_of% h1, SP.map_comp,
    SP.map_comp, ← SP.map_comp_assoc, Iso.hom_inv_id, SP.map_id, Category.id_comp,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, ← comp_whiskerRight_assoc, hbr,
    comp_whiskerRight_assoc, h2, Iso.hom_inv_id_assoc]

/-- **The first identity of the universal kernel, reduced to a pairing** (blueprint
`lemma-nearby-cycles-universal-kernel`, `𝔥 S(λ_K) = λ_{K'} ρ`): for a lax monoidal `S_P`, the map
`𝔥 : S_P RHom(A, B) ⟶ RHom(A', B')` adjoint to `(a ⊗ 1) ≫ μ ≫ S_P(ev) ≫ b` and
`λ_K : P ⟶ RHom(A, B)`, `λ_{K'} : P' ⟶ RHom(A', B')`, the identity holds as soon as the adjoint
pairings agree: `(a ⊗ 1) ≫ μ ≫ S_P(λ_K^♭) ≫ b = (1 ⊗ ρ) ≫ λ_{K'}^♭`. -/
theorem map_comp_eq_comp_of_pairing {CP CP' : Type*} [Category CP] [Category CP']
    [MonoidalCategory CP] [MonoidalCategory CP'] [MonoidalClosed CP] [MonoidalClosed CP']
    {SP : CP ⥤ CP'} [SP.LaxMonoidal] {A B P : CP} {A' B' P' : CP'} (a : A' ⟶ SP.obj A)
    (b : SP.obj B ⟶ B') (lamK : P ⟶ (ihom A).obj B) (lamK' : P' ⟶ (ihom A').obj B')
    (h : SP.obj ((ihom A).obj B) ⟶ (ihom A').obj B')
    (hh : MonoidalClosed.uncurry h = a ▷ SP.obj ((ihom A).obj B) ≫
      Functor.LaxMonoidal.μ SP A ((ihom A).obj B) ≫ SP.map ((ihom.ev A).app B) ≫ b)
    (ρ : SP.obj P ⟶ P')
    (hpair : a ▷ SP.obj P ≫ Functor.LaxMonoidal.μ SP A P ≫
      SP.map (MonoidalClosed.uncurry lamK) ≫ b =
      A' ◁ ρ ≫ MonoidalClosed.uncurry lamK') :
    SP.map lamK ≫ h = ρ ≫ lamK' := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left, hh, ← hpair,
    whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_right_assoc, ← SP.map_comp_assoc,
    ← MonoidalClosed.uncurry_eq]

/-- **The pairing identity of the universal kernel**, abstractly (the computation behind the first
identity of blueprint `lemma-nearby-cycles-universal-kernel`): for the Künneth–Verdier pairings
`p_K : p₂^* K ⊗ (p₁^* K ⊗ p₂^* D K) ⟶ p₁^! K` (the symmetry, `μ` of `p₂^*`, `p₂^*(ev)` and the
exceptional Künneth map `κ`) and its special analogue, `Π = (α_{p₁} ⊗ α_{p₂}) ≫ μ` and
`ρ = Π⁻¹ ≫ (1 ⊠ δ_K)`, the pairing is specialized:
`(α_{p₂} ⊗ 1) ≫ μ ≫ S_P(p_K) ≫ β_{p₁} = (1 ⊗ ρ) ≫ p_{K'}`, given the definition of `δ_K`,
the monoidality of `α_{p₂}`, the compatibility `hκ` of `κ` with the exchanges and the symmetry
of `S_P`. -/
theorem pairing_specialization_eq {CX CX' CP CP' : Type*} [Category CX] [Category CX']
    [Category CP] [Category CP'] [MonoidalCategory CX] [MonoidalCategory CX']
    [MonoidalClosed CX'] [MonoidalCategory CP] [MonoidalCategory CP'] [BraidedCategory CP]
    [BraidedCategory CP'] {SX : CX ⥤ CX'} [SX.LaxMonoidal] {SP : CP ⥤ CP'} [SP.LaxMonoidal]
    {L₁ L₂ R₁ : CX ⥤ CP} {L₁' L₂' R₁' : CX' ⥤ CP'}
    (α₁ : SX ⋙ L₁' ⟶ L₁ ⋙ SP) (α₂ : SX ⋙ L₂' ⟶ L₂ ⋙ SP) (β₁ : R₁ ⋙ SP ⟶ SX ⋙ R₁')
    {K DK ω : CX} {ω' : CX'} (ev : K ⊗ DK ⟶ ω) (θ : SX.obj ω ⟶ ω')
    (μ₂ : L₂.obj K ⊗ L₂.obj DK ⟶ L₂.obj (K ⊗ DK))
    (μ₂' : ∀ X Y : CX', L₂'.obj X ⊗ L₂'.obj Y ⟶ L₂'.obj (X ⊗ Y))
    (hμ₂' : ∀ {Y Y' : CX'} (g : Y ⟶ Y'), L₂'.obj (SX.obj K) ◁ L₂'.map g ≫
      μ₂' (SX.obj K) Y' = μ₂' (SX.obj K) Y ≫ L₂'.map (SX.obj K ◁ g))
    (κ : L₁.obj K ⊗ L₂.obj ω ⟶ R₁.obj K)
    (κ' : L₁'.obj (SX.obj K) ⊗ L₂'.obj ω' ⟶ R₁'.obj (SX.obj K))
    (δ : SX.obj DK ⟶ (ihom (SX.obj K)).obj ω')
    (hδ : SX.obj K ◁ δ ≫ (ihom.ev (SX.obj K)).app ω' =
      Functor.LaxMonoidal.μ SX K DK ≫ SX.map ev ≫ θ)
    (hα₂ : (α₂.app K ⊗ₘ α₂.app DK) ≫ Functor.LaxMonoidal.μ SP _ _ ≫ SP.map μ₂ =
      μ₂' _ _ ≫ L₂'.map (Functor.LaxMonoidal.μ SX K DK) ≫ α₂.app (K ⊗ DK))
    (hκ : (α₁.app K ⊗ₘ α₂.app ω) ≫ Functor.LaxMonoidal.μ SP _ _ ≫ SP.map κ ≫ β₁.app K =
      L₁'.obj (SX.obj K) ◁ L₂'.map θ ≫ κ')
    (hbr : ∀ X Y : CP, Functor.LaxMonoidal.μ SP X Y ≫ SP.map (β_ X Y).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ SP Y X)
    (Km : L₁'.obj (SX.obj K) ⊗ L₂'.obj (SX.obj DK) ⟶ SP.obj (L₁.obj K ⊗ L₂.obj DK))
    (hKm : Km = (α₁.app K ⊗ₘ α₂.app DK) ≫ Functor.LaxMonoidal.μ SP _ _) [IsIso Km] :
    α₂.app K ▷ SP.obj (L₁.obj K ⊗ L₂.obj DK) ≫ Functor.LaxMonoidal.μ SP _ _ ≫
        SP.map ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ μ₂) ≫
          (_ ◁ L₂.map ev) ≫ κ) ≫ β₁.app K =
      L₂'.obj (SX.obj K) ◁ (inv Km ≫ L₁'.obj (SX.obj K) ◁ L₂'.map δ) ≫
        ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ μ₂' _ _) ≫
          (_ ◁ L₂'.map ((ihom.ev (SX.obj K)).app ω')) ≫ κ') := by
  rw [← cancel_epi (L₂'.obj (SX.obj K) ◁ Km), ← whiskerLeft_comp_assoc _ Km,
    IsIso.hom_inv_id_assoc]
  have hR : L₂'.obj (SX.obj K) ◁ L₁'.obj (SX.obj K) ◁ L₂'.map δ ≫ (α_ _ _ _).inv ≫
      ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ μ₂' _ _) ≫
      (_ ◁ L₂'.map ((ihom.ev (SX.obj K)).app ω')) ≫ κ' =
      (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
      L₁'.obj (SX.obj K) ◁ (μ₂' _ _ ≫ L₂'.map (Functor.LaxMonoidal.μ SX K DK) ≫
        L₂'.map (SX.map ev)) ≫ L₁'.obj (SX.obj K) ◁ L₂'.map θ ≫ κ' := by
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc,
      ← whiskerLeft_comp_assoc, hμ₂' δ, Category.assoc, ← L₂'.map_comp, hδ]
    simp
  rw [hR, ← hκ]
  subst hKm
  have hn := α₂.naturality ev
  dsimp at hn
  rw [← whiskerLeft_comp_assoc, whiskerLeft_comp_tensorHom_assoc, Category.assoc, Category.assoc,
    hn, ← reassoc_of% hα₂]
  simp only [Functor.map_comp, Category.assoc, whiskerLeft_comp]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  dsimp only [Functor.comp_obj]
  have hc :=
    Functor.LaxMonoidal.μ_comp_map_braiding_exchange hbr (L₂.obj K) (L₁.obj K) (L₂.obj DK)
  simp only [Functor.map_comp] at hc
  rw [reassoc_of% hc, ← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp_assoc,
    whiskerRight_whiskerLeft_braiding_comp_assoc]
  simp

/-- **Nearby cycles of the universal kernel**, first identity, abstractly (blueprint
`lemma-nearby-cycles-universal-kernel`, `𝔥 S(λ_K) = λ_{K'} ρ`): let `λ_K` and `λ_{K'}` be the
curried Künneth–Verdier pairings (the symmetry, `μ` of `p₂^*`, `p₂^*(ev)` and the exceptional
Künneth map `κ`), `ρ = Π⁻¹ ≫ (1 ⊠ δ_K)` for `Π = (α_{p₁} ⊗ α_{p₂}) ≫ μ`, and `𝔥` the map adjoint to
`(α_{p₂} ⊗ 1) ≫ μ ≫ S(ev) ≫ β_{p₁}`. Then `𝔥 ∘ S(λ_K) = λ_{K'} ∘ ρ`, given the definition of `δ_K`,
the monoidality of `α_{p₂}`, the compatibility `hκ` of `κ` with the exchanges and the symmetry of
the lax tensor maps of `S_P`. -/
theorem map_curry_kunnethPairing_comp_eq {CX CX' CP CP' : Type*} [Category CX] [Category CX']
    [Category CP] [Category CP'] [MonoidalCategory CX] [MonoidalCategory CX']
    [MonoidalClosed CX'] [MonoidalCategory CP] [MonoidalCategory CP'] [BraidedCategory CP]
    [BraidedCategory CP'] [MonoidalClosed CP] [MonoidalClosed CP'] {SX : CX ⥤ CX'}
    [SX.LaxMonoidal] {SP : CP ⥤ CP'} [SP.LaxMonoidal]
    {L₁ L₂ R₁ : CX ⥤ CP} {L₁' L₂' R₁' : CX' ⥤ CP'}
    (α₁ : SX ⋙ L₁' ⟶ L₁ ⋙ SP) (α₂ : SX ⋙ L₂' ⟶ L₂ ⋙ SP) (β₁ : R₁ ⋙ SP ⟶ SX ⋙ R₁')
    {K DK ω : CX} {ω' : CX'} (ev : K ⊗ DK ⟶ ω) (θ : SX.obj ω ⟶ ω')
    (μ₂ : L₂.obj K ⊗ L₂.obj DK ⟶ L₂.obj (K ⊗ DK))
    (μ₂' : ∀ X Y : CX', L₂'.obj X ⊗ L₂'.obj Y ⟶ L₂'.obj (X ⊗ Y))
    (hμ₂' : ∀ {Y Y' : CX'} (g : Y ⟶ Y'), L₂'.obj (SX.obj K) ◁ L₂'.map g ≫
      μ₂' (SX.obj K) Y' = μ₂' (SX.obj K) Y ≫ L₂'.map (SX.obj K ◁ g))
    (κ : L₁.obj K ⊗ L₂.obj ω ⟶ R₁.obj K)
    (κ' : L₁'.obj (SX.obj K) ⊗ L₂'.obj ω' ⟶ R₁'.obj (SX.obj K))
    (δ : SX.obj DK ⟶ (ihom (SX.obj K)).obj ω')
    (hδ : SX.obj K ◁ δ ≫ (ihom.ev (SX.obj K)).app ω' =
      Functor.LaxMonoidal.μ SX K DK ≫ SX.map ev ≫ θ)
    (hα₂ : (α₂.app K ⊗ₘ α₂.app DK) ≫ Functor.LaxMonoidal.μ SP _ _ ≫ SP.map μ₂ =
      μ₂' _ _ ≫ L₂'.map (Functor.LaxMonoidal.μ SX K DK) ≫ α₂.app (K ⊗ DK))
    (hκ : (α₁.app K ⊗ₘ α₂.app ω) ≫ Functor.LaxMonoidal.μ SP _ _ ≫ SP.map κ ≫ β₁.app K =
      L₁'.obj (SX.obj K) ◁ L₂'.map θ ≫ κ')
    (hbr : ∀ X Y : CP, Functor.LaxMonoidal.μ SP X Y ≫ SP.map (β_ X Y).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ SP Y X)
    (Km : L₁'.obj (SX.obj K) ⊗ L₂'.obj (SX.obj DK) ⟶ SP.obj (L₁.obj K ⊗ L₂.obj DK))
    (hKm : Km = (α₁.app K ⊗ₘ α₂.app DK) ≫ Functor.LaxMonoidal.μ SP _ _) [IsIso Km]
    (h : SP.obj ((ihom (L₂.obj K)).obj (R₁.obj K)) ⟶
      (ihom (L₂'.obj (SX.obj K))).obj (R₁'.obj (SX.obj K)))
    (hh : MonoidalClosed.uncurry h = α₂.app K ▷ _ ≫ Functor.LaxMonoidal.μ SP _ _ ≫
      SP.map ((ihom.ev (L₂.obj K)).app (R₁.obj K)) ≫ β₁.app K) :
    SP.map (MonoidalClosed.curry ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (_ ◁ μ₂) ≫ (_ ◁ L₂.map ev) ≫ κ)) ≫ h =
      (inv Km ≫ L₁'.obj (SX.obj K) ◁ L₂'.map δ) ≫
        MonoidalClosed.curry ((α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
          (_ ◁ μ₂' _ _) ≫ (_ ◁ L₂'.map ((ihom.ev (SX.obj K)).app ω')) ≫ κ') := by
  refine map_comp_eq_comp_of_pairing (SP := SP) (A := L₂.obj K) (B := R₁.obj K)
    (P := L₁.obj K ⊗ L₂.obj DK) (α₂.app K) (β₁.app K) _ _ h hh _ ?_
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  exact pairing_specialization_eq α₁ α₂ β₁ ev θ μ₂ μ₂' hμ₂' κ κ' δ hδ hα₂ hκ hbr Km hKm

variable [MonoidalCategory CX] [MonoidalCategory CX'] [MonoidalClosed CX']

/-- **The restriction of `ρ` to the diagonal**, abstractly: let `Km = Π : Q' ⟶ S_P P` be invertible,
`b : Q' ⟶ P'` (the map `1 ⊠ δ`), and `εP : U P ≅ K ⊗ N`, `εQ : U' Q' ≅ S_X K ⊗ N'`,
`εP' : U' P' ≅ S_X K ⊗ D'` the restrictions of the external products to the diagonal. If
`U'(Π)` is the lax tensor map `μ` along these identifications, `U'(b)` is `S_X K ◁ δ`, and `δ` is
the adjoint of the pairing `θ ∘ S_X(ev) ∘ μ`, then `U'(Π⁻¹ ≫ b)` followed by the evaluation is
`α ≫ S_X(εP ≫ ev) ≫ θ`. -/
theorem map_comp_ev_eq_of_kunneth {U : CP ⥤ CX} {U' : CP' ⥤ CX'} {SP : CP ⥤ CP'}
    {SX : CX ⥤ CX'} (α : SP ⋙ U' ⟶ U ⋙ SX) {P : CP} {Q' P' : CP'} {K N ω : CX} {N' : CX'}
    {ω' : CX'} (εP : U.obj P ≅ K ⊗ N) (εQ : U'.obj Q' ≅ SX.obj K ⊗ N')
    (εP' : U'.obj P' ≅ SX.obj K ⊗ (ihom (SX.obj K)).obj ω')
    (μ : SX.obj K ⊗ N' ⟶ SX.obj (K ⊗ N)) (ev : K ⊗ N ⟶ ω) (θ : SX.obj ω ⟶ ω')
    (δ : N' ⟶ (ihom (SX.obj K)).obj ω')
    (hδ : SX.obj K ◁ δ ≫ (ihom.ev (SX.obj K)).app ω' = μ ≫ SX.map ev ≫ θ)
    (Km : Q' ⟶ SP.obj P) [IsIso Km]
    (hKm : U'.map Km ≫ α.app P ≫ SX.map εP.hom = εQ.hom ≫ μ)
    (b : Q' ⟶ P') (hb : U'.map b ≫ εP'.hom = εQ.hom ≫ SX.obj K ◁ δ) :
    U'.map (inv Km ≫ b) ≫ εP'.hom ≫ (ihom.ev (SX.obj K)).app ω' =
      α.app P ≫ SX.map (εP.hom ≫ ev) ≫ θ := by
  rw [Functor.map_comp, Category.assoc, reassoc_of% hb, hδ]
  have h : U'.map (inv Km) ≫ εQ.hom ≫ μ = α.app P ≫ SX.map εP.hom := by
    rw [← hKm, ← U'.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% h, SX.map_comp, Category.assoc]

end CategoryTheory

open Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section KunnethRetraction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {P : NearbyCyclesModel Z Z'}
  {f₁ f₂ : Z ⟶ X} {f₁' f₂' : Z' ⟶ X'} {d : X ⟶ Z} {d' : X' ⟶ Z'}

/-- `leftDerivedUpperStarCompOfEq` is `leftDerivedUpperStarComp` up to `eqToHom`, inverse form. -/
lemma leftDerivedUpperStarCompOfEq_inv_app_eq {B₀ B₁ B₂ : Scheme.{u}} (p : B₀ ⟶ B₁) (q : B₁ ⟶ B₂)
    {pq : B₀ ⟶ B₂} (w : p ≫ q = pq)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology B₂) Ab.{u + 1}) (condensedRingObj Λ B₂))) :
    (leftDerivedUpperStarCompOfEq Λ w).inv.app K =
      (leftDerivedUpperStarComp Λ p q).inv.app K ≫ eqToHom (by rw [w]) := by
  subst w
  simp only [eqToHom_refl, Category.comp_id]
  rfl

-- the instance of the abstract computation is matched against the unfolded Künneth maps
/-- **The Künneth map along a common section of the two projections**: for morphisms of models
`φ₁ φ₂ : P ⟶ M` and `ρ : M ⟶ P` with `ρ ≫ φ₁ = ρ ≫ φ₂ = 𝟙`, the pullback of the Künneth map
`Π_{A,B}` along `ρ`, followed by the pullback exchange `α_ρ`, is the lax tensor map `μ_M`, through
the identifications `L(d)^* L(f_i)^* ≅ L(𝟙)^* ≅ 𝟭`. -/
lemma NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction
    (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom M f₂ f₂') (ρ : M.Hom P d d')
    (htot₁ : ρ.total ≫ φ₁.total = 𝟙 _) (hgen₁ : ρ.generic ≫ φ₁.generic = 𝟙 _)
    (htot₂ : ρ.total ≫ φ₂.total = 𝟙 _) (hgen₂ : ρ.generic ≫ φ₂.generic = 𝟙 _)
    (hb₁ : d ≫ f₁ = 𝟙 X) (hs₁ : d' ≫ f₁' = 𝟙 X') (hb₂ : d ≫ f₂ = 𝟙 X) (hs₂ : d' ≫ f₂' = 𝟙 X')
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    L((d')^*⟦Λ⟧).map (NearbyCyclesModel.kunnethMap Λ φ₁ φ₂ A B) ≫
        (ρ.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫
        (M.nearbyCycles Λ).map (Functor.OplaxMonoidal.δ L((d)^*⟦Λ⟧) _ _ ≫
          (((leftDerivedUpperStarComp Λ d f₁).inv.app A ≫ eqToHom (by rw [hb₁]) ≫
              (leftDerivedUpperStarId Λ X).hom.app A) ⊗ₘ
            ((leftDerivedUpperStarComp Λ d f₂).inv.app B ≫ eqToHom (by rw [hb₂]) ≫
              (leftDerivedUpperStarId Λ X).hom.app B))) =
      Functor.OplaxMonoidal.δ L((d')^*⟦Λ⟧) _ _ ≫
        (((leftDerivedUpperStarComp Λ d' f₁').inv.app _ ≫ eqToHom (by rw [hs₁]) ≫
            (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj A)) ⊗ₘ
          ((leftDerivedUpperStarComp Λ d' f₂').inv.app _ ≫ eqToHom (by rw [hs₂]) ≫
            (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj B))) ≫
        M.tensorMap Λ A B := by
  have h := NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂
    (NearbyCyclesModel.Hom.id M) (NearbyCyclesModel.Hom.id M) (NearbyCyclesModel.Hom.id M)
    (NearbyCyclesModel.Hom.id M) ρ
    (by rw [NearbyCyclesModel.Hom.id_total, Category.comp_id, htot₁])
    (by rw [NearbyCyclesModel.Hom.id_generic, Category.comp_id, hgen₁])
    (by rw [NearbyCyclesModel.Hom.id_total, Category.comp_id, htot₂])
    (by rw [NearbyCyclesModel.Hom.id_generic, Category.comp_id, hgen₂])
    (by rw [Category.comp_id, hb₁]) (by rw [Category.comp_id, hs₁])
    (by rw [Category.comp_id, hb₂]) (by rw [Category.comp_id, hs₂]) A B
  -- the identity components
  have hc := fun C ↦ CategoryTheory.map_comp_comp_map_of_isoId (M.nearbyCycles Λ)
    (leftDerivedUpperStarId Λ X') (leftDerivedUpperStarId Λ X) C
    (NearbyCyclesModel.Hom.id_pullbackExchange_app Λ M C)
    (NearbyCyclesModel.Hom.id_pullbackExchange_app Λ M _)
  simp only [NearbyCyclesModel.kunnethMap] at h ⊢
  have hnat := NearbyCyclesModel.tensorMap_natural Λ M
    ((leftDerivedUpperStarId Λ X).hom.app (L((𝟙 X)^*⟦Λ⟧).obj A) ≫
      (leftDerivedUpperStarId Λ X).hom.app A)
    ((leftDerivedUpperStarId Λ X).hom.app (L((𝟙 X)^*⟦Λ⟧).obj B) ≫
      (leftDerivedUpperStarId Λ X).hom.app B)
  have hcA := hc A
  have hcB := hc B
  have ecA := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hb₁ A).trans
    (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d f₁ hb₁ A)
  have ecB := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hb₂ B).trans
    (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d f₂ hb₂ B)
  have ec'A := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hs₁
    ((M.nearbyCycles Λ).obj A)).trans (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d' f₁' hs₁ _)
  have ec'B := (pullbackSquareComparison_hom_app_comp_leftDerivedUpperStarId Λ hs₂
    ((M.nearbyCycles Λ).obj B)).trans (leftDerivedUpperStarCompOfEq_inv_app_eq Λ d' f₂' hs₂ _)
  apply_by_match CategoryTheory.kunneth_retraction_aux [h := h, hnat := hnat, hcA := hcA,
    hcB := hcB, ecA := ecA, ecB := ecB, ec'A := ec'A, ec'B := ec'B]

end KunnethRetraction

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k).Prime] in
/-- The deformation to the normal cone of `x` is a trait model over the base. -/
lemma isTraitModelOfBase_deformationModel :
    (deformationModel X x.left.ker k').IsTraitModelOfBase k
      (deformationTotalToTrait X x.left.ker k') (deformationGenericToPoint X x.left.ker k') :=
  .of_isPullback ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      isPullback_deformationSpecialFibre X _ k'⟩ ⟨deformationTotalToBase X _ k', rfl,
        deformationTotalToBase_hom X _ k'⟩
    (isPullback_deformationModel_ε k' x.left.ker)

variable (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)

/-- The duality map `δ_K : Sp_{X,x}(D K) ⟶ D Sp_{X,x}(K)` of the specialization (blueprint
`proposition-nearby-cycles-commute-verdier-duality`), for a family of dualizing maps `D`. -/
noncomputable def specializationDualityMap (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specialization k' x).obj (verdierDual ℓ K) ⟶ verdierDual ℓ ((specialization k' x).obj K) :=
  NearbyCyclesModel.nearbyDualityMap ℓ D (isTraitModelOfBase_deformationModel k' x) K

/-- The comparison `ρ = (1 ⊠ δ_K) ∘ Π⁻¹ : Ψ_{X×X}(K ⊠ D K) ⟶ Ψ_X K ⊠ D Ψ_X K` of the universal
kernels (blueprint `lemma-nearby-cycles-universal-kernel`). -/
noncomputable def universalKernelSpecialization
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specializationProd k' x).obj (externalProduct ℓ K (verdierDual ℓ K)) ⟶
      externalProduct ℓ ((specialization k' x).obj K)
        (verdierDual ℓ ((specialization k' x).obj K)) :=
  inv (specializationKunnethMap k' x K (verdierDual ℓ K)) ≫
    _ ◁ (boundedConstructibleUpperStar _ ℓ _).map (specializationDualityMap k' x D K)

end AlgebraicGeometry.ProEtale.CondensedRing
