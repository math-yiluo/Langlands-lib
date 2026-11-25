/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProperBdc

/-!

# The compactification route and the fixed-square route to `R(c ∘ ι ∘ j)_*`

Let `j : B ⟶ F`, `ι : F ⟶ C`, `c : C ⟶ Y`, `d : F ⟶ X` and `Δ : X ⟶ Y` with `ι ≫ c = d ≫ Δ`, and
let `c = h ≫ p` be a factorization with `h` an open immersion and `p` proper. When `ι`, `Δ`, `j`,
`j ≫ ι`, `j ≫ d`, `(j ≫ ι) ≫ h`, … are proper, there are two identifications of `Rc_! R(j ≫ ι)_*`
with the pushforward along `j ≫ ι ≫ c = j ≫ d ≫ Δ`:

* the *compactification route* `Rc_! R(ιj)_* ≅ Rp_* h_! R(ιj)_* ≅ Rp_* R(hιj)_* ≅ R(phιj)_*`,
  through `compactificationLowerShriekIso` and the composite
  `φ : h_! Rg_* ≅ Rh_! Rg_* ≅ Rh_! Rg_! ≅ R(hg)_! ≅ R(hg)_*` (`openProperExtension`);
* the *fixed-square route* `Rc_! Rι_* Rj_* ≅ RΔ_* Rd_! Rj_* ≅ RΔ_* Rd_! Rj_! ≅ RΔ_* R(dj)_!
  ≅ RΔ_* R(dj)_* ≅ R(Δdj)_*`, through the composition isomorphism
  `Ξ = lowerStarLowerShriekCompIso` of the square.

Both agree with the *normal form* `Rc_! R(ιj)_* ≅ Rc_! R(ιj)_! ≅ R(cιj)_! ≅ R(cιj)_*`
(`compactificationRoute_eq_normalForm`, `fixedSquareRoute_eq_normalForm`), hence with each other
(`compactificationRoute_eq_fixedSquareRoute`). The proofs only use the coherences of the lower
shriek on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` recorded in `BaseChangeTheorems.LowerShriek.Coherence` (associativity
of the composition isomorphisms and their compatibility with `Rf_! ≅ Rf_*`).

On the ambient derived categories, the compactification route of `ExchangeOnProperBdc` (through
`closedExtension : h_! g_* ⟶ (hg)_*` and `lowerStarCompOfEq`) is the underlying morphism of the
`Dᵇc` route (`compactificationRoute_ambient`), hence of the fixed-square route
(`compactificationRoute_ambient_eq_fixedSquareRoute`), as soon as `openProperExtension` is adjoint
to the inverse of the base change map (`closedExtension_app_eq_openProperExtension`). That
hypothesis is proved in `CompactificationRouteClosedExtension`.

The abstract computations (`CategoryTheory.map_openProperExtension_comp_counit`,
`CategoryTheory.map_unit_comp_inv_comp_baseChange_eq_id`, …) are stated for arbitrary adjunctions
and natural isomorphisms; the `Dᵇc` statements are instances of them.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section OpenProperExtensionAbstract

variable {𝔅 ℭ 𝔓 : Type*} [Category 𝔅] [Category ℭ] [Category 𝔓]
  {Sg Rg : 𝔅 ⥤ ℭ} {Lg : ℭ ⥤ 𝔅} {Sh Eh : ℭ ⥤ 𝔓} {Sq Rq : 𝔅 ⥤ 𝔓} {Lq : 𝔓 ⥤ 𝔅} {S1 : 𝔅 ⥤ 𝔅}
  (ag : Lg ⊣ Rg) (aq : Lq ⊣ Rq) (Pg : Sg ≅ Rg) (Pq : Sq ≅ Rq) (Oh : Sh ≅ Eh) (ι1 : S1 ≅ 𝟭 𝔅)
  (C : Sq ≅ Sg ⋙ Sh) (Sig : Sg ⋙ Sh ⟶ S1 ⋙ Sq)
  (hSig : ∀ N, Sig.app N ≫ Sq.map (ι1.hom.app N) = C.inv.app N) (Ex : Sh ⋙ Lq ⟶ Lg ⋙ S1)
  (hEx : Ex = (mateEquiv (ag.ofNatIsoRight Pg.symm) (aq.ofNatIsoRight Pq.symm)).symm Sig)

include hSig hEx in
/-- **The adjoint of `h_! g_* ≅ R(gh)_*` through the compact-support base change**: for
`φ = O_h⁻¹ ≫ h_!(P_g⁻¹) ≫ C⁻¹ ≫ P_q : E_h R_g ⟶ R_q` (`q = g ≫ h`), if the compact-support base
change `Ex : S_h ⋙ L_q ⟶ L_g ⋙ S_𝟙` is the mate of `Σ : S_g ⋙ S_h ⟶ S_𝟙 ⋙ S_q` (with
`Σ ≫ S_q(ι_𝟙) = C⁻¹`), then the adjoint `L_q(φ) ≫ ε_q` of `φ` is
`L_q(O_h⁻¹) ≫ Ex ≫ S_𝟙(ε_g) ≫ ι_𝟙`. -/
lemma map_openProperExtension_comp_counit (N : 𝔅) :
    Lq.map (Oh.inv.app (Rg.obj N) ≫ Sh.map (Pg.inv.app N) ≫ C.inv.app N ≫ Pq.hom.app N) ≫
        aq.counit.app N =
      Lq.map (Oh.inv.app (Rg.obj N)) ≫ Ex.app (Rg.obj N) ≫ S1.map (ag.counit.app N) ≫
        ι1.hom.app N := by
  have hm := mateEquiv_counit_symm (ag.ofNatIsoRight Pg.symm) (aq.ofNatIsoRight Pq.symm) Sig N
  rw [← hEx] at hm
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.id_obj,
    Iso.symm_inv, Functor.map_comp] at hm
  have hε := (aq.ofNatIsoRight Pq.symm).counit.naturality (ι1.hom.app N)
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.id_obj,
    Iso.symm_inv, Functor.comp_map, Functor.id_map, Category.assoc] at hε
  have hn := Ex.naturality (Pg.inv.app N)
  simp only [Functor.comp_map] at hn
  rw [← hSig]
  simp only [Functor.map_comp, Category.assoc]
  rw [hε, reassoc_of% hm, reassoc_of% hn, ← S1.map_comp_assoc]
  simp only [← Lg.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]


/-- Removing identities `𝟙 ≫ F(𝟙) ≫ F(G(𝟙)) ≫ c = c`, with the objects matched up to
definitional equality. -/
lemma id_comp_map_id_comp_map_map_id {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    (F : 𝒟 ⥤ ℰ) (G : 𝒞 ⥤ 𝒟) (X : 𝒞) {Y : ℰ} (c : F.obj (G.obj X) ⟶ Y) :
    𝟙 (F.obj (G.obj X)) ≫ F.map (𝟙 (G.obj X)) ≫ F.map (G.map (𝟙 X)) ≫ c = c := by
  simp

/-- The underlying morphism of `eqToHom` in a full subcategory. -/
lemma ObjectProperty.FullSubcategory.hom_eqToHom {𝒞 : Type*} [Category 𝒞] {P : ObjectProperty 𝒞}
    {X Y : P.FullSubcategory} (e : X = Y) :
    (eqToHom e).hom = eqToHom (congrArg (·.obj) e) := by
  subst e
  rfl

/-- **The adjunction property of an extension, from its adjoint**: let `b : Rq ⋙ Lh ⟶ Rg` be a
base change map characterized by `Lg(b) ≫ ε_g = c⁻¹ ≫ ε_q` (`c : Lq ≅ Lh ⋙ Lg`). If
`φ : Eh Rg N ⟶ Rq N` has adjoint `Lq(φ) ≫ ε_q = T ≫ S₁(ε_g) ≫ ι₁` and
`Lg(η_h) ≫ c⁻¹ ≫ T ≫ ι₁ = 𝟙` at `Rg N`, then `η_h ≫ Lh(φ) ≫ b = 𝟙` at `Rg N`. -/
lemma unit_comp_map_comp_baseChange_eq_id {𝔅 ℭ 𝔓 : Type*} [Category 𝔅] [Category ℭ]
    [Category 𝔓] {Rg : 𝔅 ⥤ ℭ} {Lg : ℭ ⥤ 𝔅} {Eh : ℭ ⥤ 𝔓} {Lh : 𝔓 ⥤ ℭ} {Rq : 𝔅 ⥤ 𝔓}
    {Lq : 𝔓 ⥤ 𝔅} {S1 : 𝔅 ⥤ 𝔅} (ag : Lg ⊣ Rg) (aq : Lq ⊣ Rq) (ah : Eh ⊣ Lh) (cq : Lq ≅ Lh ⋙ Lg)
    (ι1 : S1 ≅ 𝟭 𝔅) (b : Rq ⋙ Lh ⟶ Rg)
    (hb : ∀ N, Lg.map (b.app N) ≫ ag.counit.app N = cq.inv.app (Rq.obj N) ≫ aq.counit.app N)
    (N : 𝔅) (φ : Eh.obj (Rg.obj N) ⟶ Rq.obj N)
    (T : Lq.obj (Eh.obj (Rg.obj N)) ⟶ S1.obj (Lg.obj (Rg.obj N)))
    (hφ : Lq.map φ ≫ aq.counit.app N = T ≫ S1.map (ag.counit.app N) ≫ ι1.hom.app N)
    (hT : Lg.map (ah.unit.app (Rg.obj N)) ≫ cq.inv.app (Eh.obj (Rg.obj N)) ≫ T ≫
      ι1.hom.app (Lg.obj (Rg.obj N)) = 𝟙 _) :
    ah.unit.app (Rg.obj N) ≫ Lh.map φ ≫ b.app N = 𝟙 _ := by
  apply (ag.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Functor.map_id,
    Category.id_comp]
  have hn := cq.inv.naturality φ
  simp only [Functor.comp_map] at hn
  have hι := ι1.hom.naturality (ag.counit.app N)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hι
  rw [hb, reassoc_of% hn, hφ, hι, reassoc_of% hT]

/-- The trivialization of an adjunction `E ⊣ L₁` of endofunctors from `S₁ ≅ E`, `S₁ ≅ R₁ ≅ 𝟭`
and `L₁ ≅ 𝟭`, given the unit identity `hc` (the form of
`boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen_of` for `j = 𝟙`):
`(S₁ ≅ 𝟭)⁻¹ ≫ (S₁ ≅ E) ≫ ε` is `L₁ ≅ 𝟭` on `L₁ W`. -/
lemma inv_app_comp_hom_app_comp_counit_of_unit {𝒳 : Type*} [Category 𝒳] {E L1 S1 R1 : 𝒳 ⥤ 𝒳}
    (aE : E ⊣ L1) (a1 : L1 ⊣ R1) (O : S1 ≅ E) (P : S1 ≅ R1) (RId : R1 ≅ 𝟭 𝒳) (UId : L1 ≅ 𝟭 𝒳)
    (hR : ∀ K, RId.hom.app K = UId.inv.app (R1.obj K) ≫ a1.counit.app K)
    (hc : ∀ M, aE.unit.app M ≫ L1.map (O.inv.app M ≫ P.hom.app M) ≫ a1.counit.app M = 𝟙 M)
    (W : 𝒳) :
    (P ≪≫ RId).inv.app (L1.obj W) ≫ O.hom.app (L1.obj W) ≫ aE.counit.app W = UId.hom.app W := by
  have hU (M : 𝒳) : aE.unit.app M ≫ UId.hom.app (E.obj M) =
      (P ≪≫ RId).inv.app M ≫ O.hom.app M := by
    have h₁ := hc M
    have hε : a1.counit.app M = UId.hom.app (R1.obj M) ≫ RId.hom.app M := by
      rw [hR, Iso.hom_inv_id_app_assoc]
    have hn := UId.hom.naturality (O.inv.app M ≫ P.hom.app M)
    simp only [Functor.id_map, Functor.id_obj] at hn
    rw [hε, ← Category.assoc (L1.map _), hn] at h₁
    rw [← cancel_mono (O.inv.app M ≫ (P ≪≫ RId).hom.app M)]
    simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Category.assoc] at h₁ ⊢
    rw [h₁]
    simp
  have hn := UId.hom.naturality (aE.counit.app W)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [← reassoc_of% (hU (L1.obj W)), ← hn, aE.right_triangle_components_assoc]

/-- **The restriction of `Ex_!` along the open immersion `h`**, abstractly: let
`BC' = exchangeLeft a_h a_1 θ : L_g ⋙ E_1 ⟶ E_h ⋙ L_q` be the extension-by-zero base change of the
square `(𝟙, g, q, h)` with `Ex ≫ O_1 ≫ BC' = L_q(O_h)` (`Ex` invertible), `θ ≫ (L_1 ≅ 𝟭) = c⁻¹`
and `(S_1 ≅ 𝟭)⁻¹ ≫ O_1 ≫ ε_1 = (L_1 ≅ 𝟭)` on `L_1`. Then
`L_g(η_h) ≫ c⁻¹ ≫ L_q(O_h⁻¹) ≫ Ex ≫ (S_1 ≅ 𝟭) = 𝟙`. -/
lemma map_unit_comp_inv_comp_baseChange_eq_id {𝔅 ℭ 𝔓 : Type*} [Category 𝔅] [Category ℭ]
    [Category 𝔓] {Lg : ℭ ⥤ 𝔅} {Eh Sh : ℭ ⥤ 𝔓} {Lh : 𝔓 ⥤ ℭ} {Lq : 𝔓 ⥤ 𝔅} {S1 E1 L1 : 𝔅 ⥤ 𝔅}
    (ah : Eh ⊣ Lh) (a1 : E1 ⊣ L1) (Oh : Sh ≅ Eh) (O1 : S1 ≅ E1) (ι1 : S1 ≅ 𝟭 𝔅)
    (UId : L1 ≅ 𝟭 𝔅) (c : Lq ≅ Lh ⋙ Lg) (θ : Lh ⋙ Lg ≅ Lq ⋙ L1) (Ex : Sh ⋙ Lq ⟶ Lg ⋙ S1)
    (BC' : Lg ⋙ E1 ⟶ Eh ⋙ Lq) (hBC' : BC' = Adjunction.exchangeLeft ah a1 θ)
    (hO : ∀ K, Ex.app K ≫ O1.hom.app (Lg.obj K) ≫ BC'.app K = Lq.map (Oh.hom.app K))
    (hθ : ∀ Z, θ.hom.app Z ≫ UId.hom.app (Lq.obj Z) = c.inv.app Z)
    (hT1 : ∀ W, ι1.inv.app (L1.obj W) ≫ O1.hom.app (L1.obj W) ≫ a1.counit.app W = UId.hom.app W)
    (K : ℭ) [IsIso (Ex.app K)] :
    Lg.map (ah.unit.app K) ≫ c.inv.app (Eh.obj K) ≫ Lq.map (Oh.inv.app K) ≫ Ex.app K ≫
      ι1.hom.app (Lg.obj K) = 𝟙 _ := by
  have hA : ι1.inv.app (Lg.obj K) ≫ O1.hom.app (Lg.obj K) ≫ BC'.app K =
      Lg.map (ah.unit.app K) ≫ c.inv.app (Eh.obj K) := by
    subst hBC'
    rw [Adjunction.exchangeLeft_app]
    have n₁ := ι1.inv.naturality (Lg.map (ah.unit.app K))
    have n₂ := O1.hom.naturality (Lg.map (ah.unit.app K))
    have n₃ := ι1.inv.naturality (θ.hom.app (Eh.obj K))
    have n₄ := O1.hom.naturality (θ.hom.app (Eh.obj K))
    simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at n₁ n₂ n₃ n₄
    rw [← reassoc_of% n₂, ← reassoc_of% n₁, ← reassoc_of% n₄, ← reassoc_of% n₃, hT1, hθ]
  have hE : BC'.app K ≫ Lq.map (Oh.inv.app K) ≫ Ex.app K = O1.inv.app (Lg.obj K) := by
    have h₁ : BC'.app K = O1.inv.app _ ≫ inv (Ex.app K) ≫ Lq.map (Oh.hom.app K) := by
      rw [← hO K]
      simp
    rw [h₁]
    simp [← Lq.map_comp_assoc]
  rw [← reassoc_of% hA, reassoc_of% hE]
  simp

/-- The form of `unit_comp_map_comp_baseChange_eq_id` with the adjoint of `φ` given as
`T' ≫ ε_g`. -/
lemma unit_comp_map_comp_baseChange_eq_id' {𝔅 ℭ 𝔓 : Type*} [Category 𝔅] [Category ℭ]
    [Category 𝔓] {Rg : 𝔅 ⥤ ℭ} {Lg : ℭ ⥤ 𝔅} {Eh : ℭ ⥤ 𝔓} {Lh : 𝔓 ⥤ ℭ} {Rq : 𝔅 ⥤ 𝔓}
    {Lq : 𝔓 ⥤ 𝔅} (ag : Lg ⊣ Rg) (aq : Lq ⊣ Rq) (ah : Eh ⊣ Lh) (cq : Lq ≅ Lh ⋙ Lg)
    (b : Rq ⋙ Lh ⟶ Rg) (N : 𝔅)
    (hb : Lg.map (b.app N) ≫ ag.counit.app N = cq.inv.app (Rq.obj N) ≫ aq.counit.app N)
    (φ : Eh.obj (Rg.obj N) ⟶ Rq.obj N) (T : Lq.obj (Eh.obj (Rg.obj N)) ⟶ Lg.obj (Rg.obj N))
    (hφ : Lq.map φ ≫ aq.counit.app N = T ≫ ag.counit.app N)
    (hT : Lg.map (ah.unit.app (Rg.obj N)) ≫ cq.inv.app (Eh.obj (Rg.obj N)) ≫ T = 𝟙 _) :
    ah.unit.app (Rg.obj N) ≫ Lh.map φ ≫ b.app N = 𝟙 _ := by
  apply (ag.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Functor.map_id,
    Category.id_comp]
  have hn := cq.inv.naturality φ
  simp only [Functor.comp_map] at hn
  rw [hb, reassoc_of% hn, hφ, reassoc_of% hT]
end OpenProperExtensionAbstract

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

section Generic

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- Transporting the inverse composition isomorphism along an equality `g = g'`. -/
@[reassoc]
lemma eqToHom_map_comp_lowerShriekComp_inv_app {f : X ⟶ Y} {g g' : Y ⟶ Z} (hg : g = g')
    {M : Dᵇc(Y.left)⟦Λℓ⟧} {L : Dᵇc(X.left)⟦Λℓ⟧}
    (φ : M ⟶ (boundedConstructibleLowerShriek ℓ f).obj L) :
    eqToHom (by rw [hg]) ≫ (boundedConstructibleLowerShriek ℓ g').map φ ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g').inv.app L =
    (boundedConstructibleLowerShriek ℓ g).map φ ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app L ≫ eqToHom (by rw [hg]) := by
  subst hg
  simp

/-- Transporting `Rf_! ≅ Rf_*` along equalities `t = t' = t''`. -/
lemma eqToHom_isoLowerStar_hom_app_eqToHom {t t' t'' : X ⟶ Y} (h₁ : t = t') (h₂ : t' = t'')
    [IsProper t'.left] [IsProper t''.left] (K : Dᵇc(X.left)⟦Λℓ⟧) :
    eqToHom (by rw [h₁]) ≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ t').hom.app K ≫
      eqToHom (by rw [h₂]) =
    (eqToHom (by rw [h₁, h₂]) : (boundedConstructibleLowerShriek ℓ t).obj K ⟶ _) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ t'').hom.app K := by
  subst h₁ h₂
  simp



/-- The inverse form of `boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp`:
`R(f ≫ g)_* ≅ Rg_* Rf_* ≅ Rg_* Rf_! ≅ Rg_! Rf_! ≅ R(f ≫ g)_!` is `(Rf_! ≅ Rf_*)⁻¹` of `f ≫ g`. -/
lemma lowerStarComp_hom_app_comp_isoLowerStar_inv (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left]
    [IsProper g.left] [IsProper (f ≫ g).left] (K : Dᵇc(X.left)⟦Λℓ⟧) :
    (boundedConstructibleLowerStar ℓ g).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app K =
    (boundedConstructibleLowerStarComp ℓ f g).hom.app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g)).inv.app K := by
  have h := boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ f g K
  rw [← cancel_mono ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g)).hom.app K),
    ← cancel_mono ((boundedConstructibleLowerStarComp ℓ f g).inv.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Iso.hom_inv_id_app]
  rw [← h]
  erw [Iso.inv_hom_id_app_assoc]
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rfl


/-- `boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp`, solved for `Rg_* (Rf_! ≅ Rf_*)`
followed by the composition isomorphism of the pushforwards. -/
@[reassoc]
lemma isoLowerStar_hom_app_comp_map_comp_lowerStarComp_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] [IsProper (f ≫ g).left] (K : Dᵇc(X.left)⟦Λℓ⟧) :
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerStar ℓ g).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) ≫
      (boundedConstructibleLowerStarComp ℓ f g).hom.app K =
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g)).hom.app K := by
  have h := boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ f g K
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K),
    reassoc_of% h]
  simp
end Generic

section Assoc

variable {W X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The inverse form of `boundedConstructibleLowerShriekComp_padicAlgCl_assoc`. -/
@[reassoc]
lemma lowerShriekComp_hom_app_comp_map_inv_comp_inv (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K : Dᵇc(W.left)⟦Λℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek ℓ h).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app K) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (f ≫ g) h).inv.app K =
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (g ≫ h)).inv.app K ≫
      eqToHom (by rw [Category.assoc]) := by
  have h₁ := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ f g h K
  have h₂ : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (g ≫ h)).hom.app K ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) =
      (eqToHom (by rw [Category.assoc]) : (boundedConstructibleLowerShriek ℓ (f ≫ g ≫ h)).obj K ⟶
        (boundedConstructibleLowerShriek ℓ ((f ≫ g) ≫ h)).obj K) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (f ≫ g) h).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ h).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K) := by
    rw [h₁, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (g ≫ h)).hom.app K),
    Iso.hom_inv_id_app_assoc, reassoc_of% h₂, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  simp

end Assoc

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

section Compactification

variable {B C P Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The identification `h_! Ra_* ≅ R(a ≫ h)_*` for an open immersion `h` and proper `a` and
`a ≫ h`: `h_! Ra_* ≅ Rh_! Ra_* ≅ Rh_! Ra_! ≅ R(a ≫ h)_! ≅ R(a ≫ h)_*`. -/
noncomputable def openProperExtension (a : B ⟶ C) (h : C ⟶ P) [IsOpenImmersion h.left]
    [IsProper a.left] [IsProper (a ≫ h).left] :
    boundedConstructibleLowerStar ℓ a ⋙ boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h ≅
      boundedConstructibleLowerStar ℓ (a ≫ h) :=
  Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
      ℓ h).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).symm _ ≪≫
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a h).symm ≪≫
    boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (a ≫ h)

/-- **The compactification route in normal form**: for `c = h ≫ p` (`h` open, `p` proper) and a
proper `a`, `Rc_! Ra_* ≅ Rp_* h_! Ra_* ≅ Rp_* R(a ≫ h)_* ≅ R((a ≫ h) ≫ p)_* = R(a ≫ c)_*`
(`compactificationLowerShriekIso`, `openProperExtension`) is
`Rc_! Ra_* ≅ Rc_! Ra_! ≅ R(a ≫ c)_! ≅ R(a ≫ c)_*`. -/
theorem compactificationRoute_eq_normalForm (a : B ⟶ C) {c : C ⟶ Y} (h : C ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion h.left] [IsProper p.left] (w : h ≫ p = c) [IsProper a.left]
    [IsProper (a ≫ h).left] [IsProper ((a ≫ h) ≫ p).left] [IsProper (a ≫ c).left]
    (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (compactificationLowerShriekIso ℓ h p w).hom.app ((boundedConstructibleLowerStar ℓ a).obj N) ≫
        (boundedConstructibleLowerStar ℓ p).map ((openProperExtension ℓ a h).hom.app N) ≫
        (boundedConstructibleLowerStarComp ℓ (a ≫ h) p).hom.app N ≫
        eqToHom (by rw [Category.assoc, w]) =
      (boundedConstructibleLowerShriek ℓ c).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).inv.app N) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a c).inv.app N ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (a ≫ c)).hom.app N := by
  subst w
  simp only [compactificationLowerShriekIso, lowerShriekCompOfEq_rfl, openProperExtension,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
    Functor.map_comp]
  simp only [← Functor.map_comp_assoc]
  rw [← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p).hom.naturality_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [(boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p).hom.naturality_assoc]
  erw [isoLowerStar_hom_app_comp_map_comp_lowerStarComp_hom_assoc ℓ (a ≫ h) p N]
  have n := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h p).hom.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).inv.app N)
  simp only [Functor.comp_map] at n
  rw [← reassoc_of% n]
  erw [lowerShriekComp_hom_app_comp_map_inv_comp_inv_assoc ℓ a h p N]
  rw [eqToHom_isoLowerStar_hom_app_eqToHom ℓ (Category.assoc a h p).symm
    (Category.assoc a h p)]
  simp

end Compactification

section FixedSquare

variable {B F C X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

-- matching the composites of `Dᵇc` functors in the rewrites is slow
/-- **The fixed-square route in normal form**: for a square `ι ≫ c = d ≫ Δ` with `ι`, `Δ` proper
and `j` with `j`, `j ≫ ι`, `j ≫ d` proper,
`Rc_! Rι_* Rj_* ≅ RΔ_* Rd_! Rj_* ≅ RΔ_* Rd_! Rj_! ≅ RΔ_* R(j ≫ d)_! ≅ RΔ_* R(j ≫ d)_*
≅ R((j ≫ d) ≫ Δ)_* = R((j ≫ ι) ≫ c)_*` (through `Ξ = lowerStarLowerShriekCompIso`) is
`Rc_! Rι_* Rj_* ≅ Rc_! R(j ≫ ι)_* ≅ Rc_! R(j ≫ ι)_! ≅ R((j ≫ ι) ≫ c)_! ≅ R((j ≫ ι) ≫ c)_*`. -/
theorem fixedSquareRoute_eq_normalForm (j : B ⟶ F) {ι : F ⟶ C} {c : C ⟶ Y} {d : F ⟶ X}
    {Δ : X ⟶ Y} (sq : ι ≫ c = d ≫ Δ) [IsProper ι.left] [IsProper Δ.left] [IsProper j.left]
    [IsProper (j ≫ ι).left] [IsProper (j ≫ d).left] [IsProper ((j ≫ d) ≫ Δ).left]
    [IsProper ((j ≫ ι) ≫ c).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (lowerStarLowerShriekCompIso ℓ sq).hom.app ((boundedConstructibleLowerStar ℓ j).obj N) ≫
        (boundedConstructibleLowerStar ℓ Δ).map
          ((boundedConstructibleLowerShriek ℓ d).map
              ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app N) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app N ≫
            (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ d)).hom.app N) ≫
        (boundedConstructibleLowerStarComp ℓ (j ≫ d) Δ).hom.app N ≫
        eqToHom (by rw [Category.assoc, ← sq, ← Category.assoc]) =
      (boundedConstructibleLowerShriek ℓ c).map
          ((boundedConstructibleLowerStarComp ℓ j ι).hom.app N) ≫
        (boundedConstructibleLowerShriek ℓ c).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ ι)).inv.app N) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (j ≫ ι) c).inv.app N ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ((j ≫ ι) ≫ c)).hom.app N := by
  simp only [lowerStarLowerShriekCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, eqToIso.hom, eqToHom_app, Category.assoc,
    Functor.map_comp]
  -- move the `RΔ_*`-part across `RΔ_! ≅ RΔ_*` and contract with the composition of `j ≫ d` and `Δ`
  rw [← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δ).hom.naturality_assoc,
    ← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δ).hom.naturality_assoc]
  rw [isoLowerStar_hom_app_comp_map_comp_lowerStarComp_hom_assoc ℓ (j ≫ d) Δ N]
  have n₁ := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ d Δ).hom.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app N)
  simp only [Functor.comp_map] at n₁
  rw [← reassoc_of% n₁]
  rw [lowerShriekComp_hom_app_comp_map_inv_comp_inv_assoc ℓ j d Δ N]
  rw [eqToHom_map_comp_lowerShriekComp_inv_app_assoc ℓ sq]
  rw [eqToHom_trans_assoc, eqToHom_isoLowerStar_hom_app_eqToHom ℓ
    (by rw [sq, Category.assoc] : j ≫ ι ≫ c = (j ≫ d) ≫ Δ)
    (by rw [Category.assoc, Category.assoc, sq])]
  have n₂ := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ ι c).inv.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app N)
  simp only [Functor.comp_map] at n₂
  simp only [← reassoc_of% n₂]
  have H : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ ι c).inv.app
        ((boundedConstructibleLowerShriek ℓ j).obj N) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j (ι ≫ c)).inv.app N ≫
      (eqToHom (by rw [Category.assoc]) : (boundedConstructibleLowerShriek ℓ (j ≫ ι ≫ c)).obj N ⟶
        (boundedConstructibleLowerShriek ℓ ((j ≫ ι) ≫ c)).obj N) =
      (boundedConstructibleLowerShriek ℓ c).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι).inv.app N) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (j ≫ ι) c).inv.app N := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ ι c).hom.app _),
      Iso.hom_inv_id_app_assoc]
    exact (lowerShriekComp_hom_app_comp_map_inv_comp_inv ℓ j ι c N).symm
  simp only [reassoc_of% H]
  have hf : (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ι).inv.app
        ((boundedConstructibleLowerStar ℓ j).obj N) ≫
      (boundedConstructibleLowerShriek ℓ ι).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app N) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι).inv.app N =
      (boundedConstructibleLowerStarComp ℓ j ι).hom.app N ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ ι)).inv.app N := by
    rw [← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ι).inv.naturality_assoc]
    exact lowerStarComp_hom_app_comp_isoLowerStar_inv ℓ j ι N
  have hf' := (boundedConstructibleLowerShriek ℓ c).congr_map hf
  simp only [Functor.map_comp] at hf'
  simp only [reassoc_of% hf']

end FixedSquare

section Routes

variable {B F C P X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The compactification route is the fixed-square route**: for a square `ι ≫ c = d ≫ Δ`
(`ι`, `Δ` proper), a factorization `c = h ≫ p` (`h` an open immersion, `p` proper) and `j` with
`j`, `j ≫ ι`, `j ≫ d`, `(j ≫ ι) ≫ h` proper, the two identifications
```
Rc_! Rι_* Rj_* ≅ Rc_! R(j ≫ ι)_* ≅ Rp_* h_! R(j ≫ ι)_* ≅ Rp_* R((j ≫ ι) ≫ h)_*
    ≅ R(((j ≫ ι) ≫ h) ≫ p)_* = R((j ≫ d) ≫ Δ)_*,
Rc_! Rι_* Rj_* ≅ RΔ_* Rd_! Rj_* ≅ RΔ_* Rd_! Rj_! ≅ RΔ_* R(j ≫ d)_! ≅ RΔ_* R(j ≫ d)_*
    ≅ R((j ≫ d) ≫ Δ)_*
```
(`compactificationLowerShriekIso`, `openProperExtension`; `Ξ = lowerStarLowerShriekCompIso`)
agree. -/
theorem compactificationRoute_eq_fixedSquareRoute (j : B ⟶ F) {ι : F ⟶ C} {c : C ⟶ Y}
    {d : F ⟶ X} {Δ : X ⟶ Y} (sq : ι ≫ c = d ≫ Δ) (h : C ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion h.left] [IsProper p.left] (w : h ≫ p = c) [IsProper ι.left]
    [IsProper Δ.left] [IsProper j.left] [IsProper (j ≫ ι).left] [IsProper (j ≫ d).left]
    [IsProper ((j ≫ d) ≫ Δ).left] [IsProper ((j ≫ ι) ≫ c).left] [IsProper ((j ≫ ι) ≫ h).left]
    [IsProper (((j ≫ ι) ≫ h) ≫ p).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructibleLowerShriek ℓ c).map
        ((boundedConstructibleLowerStarComp ℓ j ι).hom.app N) ≫
      (compactificationLowerShriekIso ℓ h p w).hom.app
        ((boundedConstructibleLowerStar ℓ (j ≫ ι)).obj N) ≫
      (boundedConstructibleLowerStar ℓ p).map ((openProperExtension ℓ (j ≫ ι) h).hom.app N) ≫
      (boundedConstructibleLowerStarComp ℓ ((j ≫ ι) ≫ h) p).hom.app N ≫
      eqToHom (by simp only [Category.assoc, w, sq]) =
    (lowerStarLowerShriekCompIso ℓ sq).hom.app ((boundedConstructibleLowerStar ℓ j).obj N) ≫
      (boundedConstructibleLowerStar ℓ Δ).map
        ((boundedConstructibleLowerShriek ℓ d).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app N) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app N ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ d)).hom.app N) ≫
      (boundedConstructibleLowerStarComp ℓ (j ≫ d) Δ).hom.app N := by
  have hB := compactificationRoute_eq_normalForm ℓ (j ≫ ι) h p w N
  have hA := fixedSquareRoute_eq_normalForm ℓ j sq N
  rw [← cancel_mono (eqToHom (by rw [Category.assoc, ← sq, ← Category.assoc]) :
      (boundedConstructibleLowerStar ℓ ((j ≫ d) ≫ Δ)).obj N ⟶
        (boundedConstructibleLowerStar ℓ ((j ≫ ι) ≫ c)).obj N)]
  simp only [Category.assoc, eqToHom_trans] at hA ⊢
  rw [hB, hA]

end Routes

section Ambient

variable {B C P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- **`closedExtension` is `openProperExtension`** on bounded constructible complexes, given that
the latter is adjoint (for `h_! ⊣ Lh^*`) to the inverse of the base change map
`Lh^* R(gh)_* ⟶ Rg_*` (`closedBaseChange`): both are then adjoint to the same morphism. -/
lemma closedExtension_app_eq_openProperExtension (g : B ⟶ C) (h : C ⟶ P)
    [IsOpenImmersion h.left] [IsProper g.left] [IsProper (g ≫ h).left] (N : Dᵇc(B.left)⟦Λℓ⟧)
    (hK : (openImmersionAdjunction ℓ h.left).unit.app (R((g.left)_*⟦Λℓ⟧).obj N.obj) ≫
        L((h.left)^*⟦Λℓ⟧).map ((openProperExtension ℓ g h).hom.app N).hom ≫
        (closedBaseChange Λℓ (rfl : g.left ≫ h.left = _)).app N.obj = 𝟙 _) :
    (closedExtension (openImmersionAdjunction ℓ h.left) (rfl : g.left ≫ h.left = _)).app N.obj =
      ((openProperExtension ℓ g h).hom.app N).hom := by
  have he := unit_comp_closedExtension_app (openImmersionAdjunction ℓ h.left)
    (rfl : g.left ≫ h.left = _) N.obj
  rw [← hK, ← Category.assoc, ← Category.assoc, cancel_mono] at he
  apply ((openImmersionAdjunction ℓ h.left).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact he


variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
/-- **The ambient compactification route is the `Dᵇc` compactification route**: the composite of
`ExchangeOnProperBdc` (`compactificationLowerShriekIso`, the compatibility isomorphisms of the
restricted functors, `closedExtension` and `lowerStarCompOfEq`) is the underlying morphism of
`Rc_! Rg_* ≅ Rp_* h_! Rg_* ≅ Rp_* R(g ≫ h)_* ≅ R((g ≫ h) ≫ p)_*` on `Dᵇc` (`openProperExtension`),
given the adjunction property `hK` of `openProperExtension`. -/
theorem compactificationRoute_ambient (g : B ⟶ C) {c : C ⟶ Y} (h : C ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion h.left] [IsProper p.left] (w : h ≫ p = c) [IsProper g.left]
    [IsProper (g ≫ h).left] (N : Dᵇc(B.left)⟦Λℓ⟧)
    (hK : (openImmersionAdjunction ℓ h.left).unit.app (R((g.left)_*⟦Λℓ⟧).obj N.obj) ≫
        L((h.left)^*⟦Λℓ⟧).map ((openProperExtension ℓ g h).hom.app N).hom ≫
        (closedBaseChange Λℓ (rfl : g.left ≫ h.left = _)).app N.obj = 𝟙 _) :
    (boundedConstructible _).ι.map ((compactificationLowerShriekIso ℓ h p w).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      (boundedConstructibleLowerStarCompatibility ℓ p).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R((p.left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R((p.left)_*⟦Λℓ⟧).map (D((h.left)_!open⟦Λℓ⟧).map
        ((boundedConstructibleLowerStarCompatibility ℓ g).hom.app N)) ≫
      R((p.left)_*⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ h.left)
        (rfl : g.left ≫ h.left = _)).app N.obj) ≫
      (lowerStarCompOfEq (Λ := Λℓ) (rfl : (g.left ≫ h.left) ≫ p.left = _)).inv.app N.obj =
    ((compactificationLowerShriekIso ℓ h p w).hom.app ((boundedConstructibleLowerStar ℓ g).obj N) ≫
      (boundedConstructibleLowerStar ℓ p).map ((openProperExtension ℓ g h).hom.app N) ≫
      (boundedConstructibleLowerStarComp ℓ (g ≫ h) p).hom.app N).hom := by
  rw [closedExtension_app_eq_openProperExtension ℓ g h N hK]
  have hc : (lowerStarCompOfEq (Λ := Λℓ) (rfl : (g.left ≫ h.left) ≫ p.left = _)).inv.app N.obj =
      ((boundedConstructibleLowerStarComp ℓ (g ≫ h) p).hom.app N).hom := by
    rw [← cancel_epi ((lowerStarCompOfEq (Λ := Λℓ)
      (rfl : (g.left ≫ h.left) ≫ p.left = _)).hom.app N.obj), Iso.hom_inv_id_app]
    have h₁ := boundedConstructibleLowerStarComp_inv_app_hom ℓ (g ≫ h) p N
    erw [← h₁, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  rw [hc]
  simp only [boundedConstructibleLowerStarCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso,
    Iso.refl_hom, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom]
  refine (congrArg (fun x ↦ (boundedConstructible _).ι.map
      ((compactificationLowerShriekIso ℓ h p w).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N)) ≫ x)
    (id_comp_map_id_comp_map_map_id R((p.left)_*⟦Λℓ⟧) D((h.left)_!open⟦Λℓ⟧)
      (R((g.left)_*⟦Λℓ⟧).obj N.obj) _)).trans ?_
  rfl
end Ambient

section Final

variable {B F C P X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

-- unifying the two routes with the hand-written statement is slow
/-- **The ambient compactification route is the fixed-square route**: the composite of
`ExchangeOnProperBdc` at `g = j ≫ ι` (`compactificationLowerShriekIso`, compatibilities,
`closedExtension`, `lowerStarCompOfEq`), preceded by `Rc_!(Rι_* Rj_* ≅ R(j ≫ ι)_*)` and followed by
the transport along `((j ≫ ι) ≫ h) ≫ p = (j ≫ d) ≫ Δ`, is the underlying morphism of the
fixed-square route `Rc_! Rι_* Rj_* ≅ RΔ_* Rd_! Rj_* ≅ RΔ_* R(j ≫ d)_* ≅ R((j ≫ d) ≫ Δ)_*`, given the
adjunction property `hK` of `openProperExtension` (`closedExtension_app_eq_openProperExtension`). -/
theorem compactificationRoute_ambient_eq_fixedSquareRoute (j : B ⟶ F) {ι : F ⟶ C} {c : C ⟶ Y}
    {d : F ⟶ X} {Δ : X ⟶ Y} (sq : ι ≫ c = d ≫ Δ) (h : C ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion h.left] [IsProper p.left] (w : h ≫ p = c) [IsProper ι.left]
    [IsProper Δ.left] [IsProper j.left] [IsProper (j ≫ ι).left] [IsProper (j ≫ d).left]
    [IsProper ((j ≫ d) ≫ Δ).left] [IsProper ((j ≫ ι) ≫ c).left] [IsProper ((j ≫ ι) ≫ h).left]
    [IsProper (((j ≫ ι) ≫ h) ≫ p).left] (N : Dᵇc(B.left)⟦Λℓ⟧)
    (hK : (openImmersionAdjunction ℓ h.left).unit.app (R(((j ≫ ι).left)_*⟦Λℓ⟧).obj N.obj) ≫
        L((h.left)^*⟦Λℓ⟧).map ((openProperExtension ℓ (j ≫ ι) h).hom.app N).hom ≫
        (closedBaseChange Λℓ (rfl : (j ≫ ι).left ≫ h.left = _)).app N.obj = 𝟙 _) :
    (boundedConstructible _).ι.map ((boundedConstructibleLowerShriek ℓ c).map
        ((boundedConstructibleLowerStarComp ℓ j ι).hom.app N)) ≫
      (boundedConstructible _).ι.map ((compactificationLowerShriekIso ℓ h p w).hom.app
        ((boundedConstructibleLowerStar ℓ (j ≫ ι)).obj N)) ≫
      (boundedConstructibleLowerStarCompatibility ℓ p).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleLowerStar ℓ (j ≫ ι)).obj N)) ≫
      R((p.left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.app
        ((boundedConstructibleLowerStar ℓ (j ≫ ι)).obj N)) ≫
      R((p.left)_*⟦Λℓ⟧).map (D((h.left)_!open⟦Λℓ⟧).map
        ((boundedConstructibleLowerStarCompatibility ℓ (j ≫ ι)).hom.app N)) ≫
      R((p.left)_*⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ h.left)
        (rfl : (j ≫ ι).left ≫ h.left = _)).app N.obj) ≫
      (lowerStarCompOfEq (Λ := Λℓ) (rfl : ((j ≫ ι).left ≫ h.left) ≫ p.left = _)).inv.app N.obj ≫
      eqToHom (by rw [show ((j ≫ ι).left ≫ h.left) ≫ p.left = ((j ≫ d) ≫ Δ).left by
        simp only [← Over.comp_left, Category.assoc, w, sq]]; rfl) =
    ((lowerStarLowerShriekCompIso ℓ sq).hom.app ((boundedConstructibleLowerStar ℓ j).obj N) ≫
      (boundedConstructibleLowerStar ℓ Δ).map
        ((boundedConstructibleLowerShriek ℓ d).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app N) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app N ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ d)).hom.app N) ≫
      (boundedConstructibleLowerStarComp ℓ (j ≫ d) Δ).hom.app N).hom := by
  have hT := compactificationRoute_ambient ℓ (j ≫ ι) h p w N hK
  refine Eq.trans ?_ (congrArg (fun x ↦ (boundedConstructible _).ι.map x)
    (compactificationRoute_eq_fixedSquareRoute ℓ j sq h p w N))
  rw [reassoc_of% hT]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  rw [ObjectProperty.FullSubcategory.hom_eqToHom]
  rfl

end Final

end AlgebraicGeometry.ProEtale.CondensedRing
