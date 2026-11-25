/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.SectionCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!

# Stalks of the pushforward along a finite étale morphism

Let `f : X ⟶ Y` be a finite étale morphism and `ȳ : P ⟶ Y` a geometric point, that is `P` is
the spectrum of a separably closed field `Ω`. For a module object `F` on `X_proét`, the stalk
`ȳ^* f_* F` of the pushforward is the product of the stalks `x̄^* F` over the points
`x̄ : P ⟶ X` over `ȳ` (`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`). The projection to
the factor of `x̄` is `ȳ^* f_* F = (x̄ ≫ f)^* f_* F ≅ x̄^* f^* f_* F ⟶ x̄^* F`, through the counit
of `f^* ⊣ f_*` (`ProEtale.CondensedRing.stalkLowerStarProj`).

The proof: `f` becomes a trivial cover `∐_S U ⟶ U` after base change along an étale
`g : U ⟶ Y` (`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`), and `ȳ`
lifts to a point `v̄ : P ⟶ U`
(`AlgebraicGeometry.Scheme.exists_comp_eq_of_weaklyEtale_of_isSepClosed`).
Along the weakly étale `g`, the pushforward commutes with the pullback
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`), compatibly with the
restrictions of stalks (`ProEtale.CondensedRing.stalkLowerStarProj_lowerStarBaseChange'`). For
the trivial cover, the restrictions along its sections are `p_*` of the units of the restrictions
to the summands (`ProEtale.CondensedRing.upperStarComp_hom_app_map_counit_eq_lowerStar_map_unit`),
which exhibit a module object on a disjoint union as the product of its restrictions
(`ProEtale.CondensedRing.isLimitFanUnitOfIsColimitCofan`). The points of `X` over `ȳ` are the
`v̄ ≫ ι_s ≫ (∐_S U ⟶ X)`, `P` being a point.

The statements are made for a scheme `P` with an isomorphism `P ≅ Spec Ω` rather than for
`Spec Ω` itself, so that they apply to `Spec (AlgebraicClosure k)` with the ring structure of
`AlgebraicClosure k` found by instance search; the two ring structures on `AlgebraicClosure k`
(as a commutative ring and through its field structure) agree only up to unfolding.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- An identity between composites of isomorphisms and morphisms, used for
`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`. -/
lemma Iso.eq_hom_comp_trans_hom {C : Type*} [Category C] {A B D E G K : C} (i : B ≅ A)
    (p : B ⟶ K) (r : A ⟶ D) (c₁ : D ≅ E) (c₂ : E ≅ G) (c₃ : G ≅ K)
    (h : i.inv ≫ p = r ≫ c₁.hom ≫ c₂.hom ≫ c₃.hom) :
    p = i.hom ≫ r ≫ (c₁ ≪≫ c₂ ≪≫ c₃).hom := by
  rw [← Iso.hom_inv_id_assoc i p, h]
  simp

/-- An identity between composites of isomorphisms and morphisms, used for
`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`. -/
lemma Iso.eq_trans_symm_hom_comp {C : Type*} [Category C] {A G K V W : C} (d : V ≅ W) (c : W ≅ A)
    (p : A ⟶ G) (q : W ⟶ G) (m : V ⟶ K) (dₛ : K ≅ G) (h₁ : c.hom ≫ p = q)
    (h₂ : q = d.inv ≫ m ≫ dₛ.hom) : p = (d ≪≫ c).symm.hom ≫ m ≫ dₛ.hom := by
  rw [← Iso.inv_hom_id_assoc c p, h₁, h₂]
  simp

/-- An identity between composites of isomorphisms and morphisms, the algebraic core of
`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`. -/
lemma Iso.eq_trans_hom_comp_trans_hom {C : Type*} [Category C] {A B D E G H K : C}
    (c₁ : A ≅ B) (c₂ : B ≅ D) (c₃ : D ≅ E) (p : E ⟶ G) (cA : G ≅ H) (cK : H ≅ K) (q : B ⟶ H)
    {r : A ⟶ H} {t : A ⟶ K} (h₁ : c₂.hom ≫ c₃.hom ≫ p = q ≫ cA.inv) (h₂ : c₁.hom ≫ q = r)
    (h₃ : r ≫ cK.hom = t) : t = (c₁ ≪≫ c₂ ≪≫ c₃).hom ≫ p ≫ (cA ≪≫ cK).hom := by
  rw [← h₃, ← h₂]
  simp [reassoc_of% h₁]

end CategoryTheory

namespace CategoryTheory.Limits

/-- A fan is a limit if it is isomorphic, through isomorphisms of the cone points and of the
factors, to a limit fan. -/
noncomputable def Fan.isLimitOfIsoLegs {C : Type*} [Category C] {ι : Type*} {X X' : C}
    {Y Y' : ι → C} {π : ∀ i, X ⟶ Y i} (h : IsLimit (Fan.mk X π)) (eX : X' ≅ X)
    (eY : ∀ i, Y i ≅ Y' i) (π' : ∀ i, X' ⟶ Y' i) (w : ∀ i, π' i = eX.hom ≫ π i ≫ (eY i).hom) :
    IsLimit (Fan.mk X' π') :=
  Fan.IsLimit.mk _ (fun s ↦ Fan.IsLimit.lift h (fun i ↦ s.proj i ≫ (eY i).inv) ≫ eX.inv)
    (fun s i ↦ by
      change _ ≫ π' i = _
      rw [w, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc]
      erw [Fan.IsLimit.fac h]
      simp)
    (fun s m hm ↦ by
      rw [← cancel_mono eX.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      refine Fan.IsLimit.hom_ext h _ _ fun i ↦ ?_
      erw [Fan.IsLimit.fac h]
      rw [← hm i, ← cancel_mono (eY i).hom]
      change _ = ((m ≫ π' i) ≫ _) ≫ _
      rw [w]
      simp)

/-- A fan indexed by `ι` is a limit if, through a bijection `e : ι → ι'` and isomorphisms of the
cone points and of the factors, it is isomorphic to a limit fan indexed by `ι'`. -/
noncomputable def Fan.isLimitOfBijectiveIso {C : Type*} [Category C] {ι ι' : Type*} (e : ι → ι')
    (he : Function.Bijective e) {X X' : C} {Z : ι' → C} {ψ : ∀ j, X ⟶ Z j}
    (h : IsLimit (Fan.mk X ψ)) {Y : ι → C} (π : ∀ i, X' ⟶ Y i) (eX : X' ≅ X)
    (eY : ∀ i, Z (e i) ≅ Y i) (w : ∀ i, π i = eX.hom ≫ ψ (e i) ≫ (eY i).hom) :
    IsLimit (Fan.mk X' π) := by
  let r : ι' → ι := Function.surjInv he.2
  have hr (j : ι') : e (r j) = j := Function.surjInv_eq he.2 j
  have hr' (i : ι) : r (e i) = i := he.1 (hr (e i))
  -- transport along `r (e i) = i`
  have key (s : Fan Y) (i i₀ : ι) (hi : i₀ = i) :
      s.proj i₀ ≫ (eY i₀).inv ≫ eqToHom (by rw [hi]) ≫ (eY i).hom = s.proj i := by
    subst hi
    simp
  refine Fan.IsLimit.mk _
    (fun s ↦ Fan.IsLimit.lift h (fun j ↦ s.proj (r j) ≫ (eY (r j)).inv ≫
      eqToHom (by rw [hr j])) ≫ eX.inv) (fun s i ↦ ?_) (fun s m hm ↦ ?_)
  · change _ ≫ π i = _
    rw [w, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc]
    erw [Fan.IsLimit.fac h]
    simp only [Category.assoc]
    have := key s i (r (e i)) (hr' i)
    convert this using 3
  · rw [← cancel_mono eX.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine Fan.IsLimit.hom_ext h _ _ fun j ↦ ?_
    erw [Fan.IsLimit.fac h]
    obtain ⟨i, rfl⟩ := he.2 j
    rw [← hm (r (e i))]
    change _ = (m ≫ π (r (e i))) ≫ _
    rw [w]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have key' (j₀ : ι') (hj : j₀ = e i) :
        ψ j₀ ≫ eqToHom (by rw [hj]) = ψ (e i) := by
      subst hj
      simp
    rw [key' _ (hr (e i))]
    rfl

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A point `y : Spec Ω ⟶ Y`, `Ω` separably closed, whose image lies in the image of a weakly
étale morphism `g : U ⟶ Y`, lifts along `g`: the fibre `Spec Ω ×_Y U` is weakly étale over
`Spec Ω` and nonempty, so it has a section. -/
lemma Scheme.exists_comp_eq_of_weaklyEtale_of_isSepClosed {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {U Y : Scheme.{u}} (g : U ⟶ Y) [WeaklyEtale g] (y : Spec (.of Ω) ⟶ Y)
    (h : y (IsLocalRing.closedPoint Ω) ∈ Set.range g) : ∃ v : Spec (.of Ω) ⟶ U, v ≫ g = y := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨t, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := g)
    (IsLocalRing.closedPoint Ω) z hz.symm
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale_of_isSepClosed (pullback.fst y g) t
  exact ⟨σ ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition, reassoc_of% hσ]⟩

/-- A finite étale morphism `f : X ⟶ Y` becomes a trivial cover `∐_S U ⟶ U` after base change
along an étale `g : U ⟶ Y` whose image contains a given point `y` (a restatement of
`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma` for the morphism `f`). -/
theorem Scheme.Hom.exists_etale_isPullback_sigma {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [Etale f] (y : Y) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Y) (_ : Etale g) (S : Type u) (_ : Finite S)
      (fst : (∐ fun _ : S ↦ U) ⟶ X),
      y ∈ Set.range g ∧ IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U) f g :=
  Scheme.FiniteEtale.exists_etale_isPullback_sigma
    (⟨Scheme.Etale.mk f, ‹IsFinite f›⟩ : Y.FiniteEtale) y

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y P : Scheme.{u}} (f : X ⟶ Y) (y : P ⟶ Y)

/-- The composition isomorphism `(a ≫ b)^* M ≅ a^* b^* M` of the pullbacks of module objects at
`M`, as an isomorphism `a^* (b^* M) ≅ (a ≫ b)^* M`. -/
noncomputable def upperStarCompApp {T Z R : Scheme.{u}} (a : T ⟶ Z) (b : Z ⟶ R)
    (M : Mod (Sheaf (Scheme.ProEt.topology R) Ab.{u + 1}) (condensedRingObj Λ R)) :
    (a)^*⟦Λ⟧.obj ((b)^*⟦Λ⟧.obj M) ≅ (a ≫ b)^*⟦Λ⟧.obj M :=
  ((upperStarComp Λ a b).app M).symm

@[simp]
lemma upperStarCompApp_hom {T Z R : Scheme.{u}} (a : T ⟶ Z) (b : Z ⟶ R)
    (M : Mod (Sheaf (Scheme.ProEt.topology R) Ab.{u + 1}) (condensedRingObj Λ R)) :
    (upperStarCompApp Λ a b M).hom = (upperStarComp Λ a b).inv.app M :=
  rfl

/-- **The stalk of a finite étale pushforward** at a geometric point `ȳ : P ⟶ Y`,
`P ≅ Spec Ω` with `Ω` separably closed: `ȳ^* f_* F` is the product of the stalks `x̄^* F` over the
points `x̄ : P ⟶ X` over `ȳ`, with the projections `stalkLowerStarProj`. -/
theorem isLimit_stalkLowerStarFan [IsFinite f] [Etale f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (eP : P ≅ Spec (.of Ω))
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Nonempty (IsLimit (Fan.mk ((y)^*⟦Λ⟧.obj ((f)_*⟦Λ⟧.obj F))
      fun x : FibrePoints f y ↦ stalkLowerStarProj Λ x.2 F)) := by
  classical
  obtain ⟨U, g, hg, S, hS, fst, hy, hpb⟩ :=
    f.exists_etale_isPullback_sigma (y (eP.inv (IsLocalRing.closedPoint Ω)))
  let fold : (∐ fun _ : S ↦ U) ⟶ U := Sigma.desc fun _ ↦ 𝟙 U
  have hpb' : IsPullback fst fold f g := hpb
  have : WeaklyEtale g := inferInstance
  have : WeaklyEtale fst := MorphismProperty.of_isPullback hpb'.flip ‹_›
  obtain ⟨v₀, hv₀⟩ := Scheme.exists_comp_eq_of_weaklyEtale_of_isSepClosed g (eP.inv ≫ y)
    (by simpa using hy)
  obtain ⟨v, hv⟩ : ∃ v : P ⟶ U, v ≫ g = y := ⟨eP.hom ≫ v₀, by simp [hv₀]⟩
  have := isIso_lowerStarBaseChange_of_isPullback Λ hpb'
  let N := (fst)^*⟦Λ⟧.obj F
  have hι (s : S) : Sigma.ι (fun _ : S ↦ U) s ≫ fold = 𝟙 U := Sigma.ι_comp_desc _ _
  -- the restrictions of `p_* N` along the sections of the trivial cover `p`
  have h5 : IsLimit (Fan.mk ((𝟙 U)^*⟦Λ⟧.obj ((fold)_*⟦Λ⟧.obj N))
      fun s ↦ stalkLowerStarProj Λ (hι s) N) := by
    have : PreservesLimitsOfShape (Discrete S) (fold)_*⟦Λ⟧ :=
      (upperStarLowerStarAdjunction Λ fold).rightAdjoint_preservesLimits.preservesLimitsOfShape
    have h1 := isLimitFanUnitOfIsColimitCofanConst Λ (coproductIsCoproduct fun _ : S ↦ U) N
    have h2 := isLimitFanMkObjOfIsLimit (fold)_*⟦Λ⟧ _ _ h1
    refine Fan.isLimitOfIsoLegs h2 ((upperStarId Λ U).app _)
      (fun s ↦ (lowerStarComp Λ (Sigma.ι (fun _ : S ↦ U) s) fold).app _ ≪≫
        (lowerStarCongr Λ (hι s)).app _ ≪≫ (lowerStarId Λ U).app _) _ fun s ↦ ?_
    have L := upperStarComp_hom_app_map_counit_eq_lowerStar_map_unit Λ
      (Sigma.ι (fun _ : S ↦ U) s) fold (hι s) N
    have L' : ((upperStarId Λ U).app ((fold)_*⟦Λ⟧.obj N)).inv ≫ stalkLowerStarProj Λ (hι s) N =
        (fold)_*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ (Sigma.ι (fun _ : S ↦ U) s)).unit.app N) ≫
          ((lowerStarComp Λ (Sigma.ι (fun _ : S ↦ U) s) fold).app _).hom ≫
          ((lowerStarCongr Λ (hι s)).app _).hom ≫ ((lowerStarId Λ U).app _).hom := by
      rw [stalkLowerStarProj_eq, Iso.app_inv, Iso.app_hom, Iso.app_hom, Iso.app_hom]
      exact L
    exact Iso.eq_hom_comp_trans_hom _ _ _ _ _ _ L'
  -- the restrictions of the stalk of `p_* N` at `v̄`
  have h4s (s : S) : (v ≫ Sigma.ι (fun _ : S ↦ U) s) ≫ fold = v := by
    rw [Category.assoc, hι, Category.comp_id]
  have h4 : IsLimit (Fan.mk ((v)^*⟦Λ⟧.obj ((fold)_*⟦Λ⟧.obj N))
      fun s ↦ stalkLowerStarProj Λ (h4s s) N) := by
    have : PreservesLimitsOfShape (Discrete S) (v)^*⟦Λ⟧ := by
      obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
      exact preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) _
    have h6 := isLimitFanMkObjOfIsLimit (v)^*⟦Λ⟧ _ _ h5
    refine Fan.isLimitOfIsoLegs h6
      (upperStarCompApp Λ v (𝟙 U) _ ≪≫ (upperStarCongr Λ (Category.comp_id v)).app _).symm
      (fun s ↦ upperStarCompApp Λ v (Sigma.ι (fun _ : S ↦ U) s) N) _ fun s ↦ ?_
    have hx' : (v ≫ Sigma.ι (fun _ : S ↦ U) s) ≫ fold = v ≫ 𝟙 U := by
      rw [h4s, Category.comp_id]
    have hcl := stalkLowerStarProj_comp_left Λ v (hι s) hx' N
    have hcong := upperStarCongr_hom_app_stalkLowerStarProj Λ (Category.comp_id v) hx' (h4s s) N
    rw [← Iso.app_hom] at hcong
    have hd : (upperStarCompApp Λ v (𝟙 U) ((fold)_*⟦Λ⟧.obj N)).inv =
        (upperStarComp Λ v (𝟙 U)).hom.app ((fold)_*⟦Λ⟧.obj N) := rfl
    exact Iso.eq_trans_symm_hom_comp _ _ _ _ _ _ hcong (by rw [hcl, hd, upperStarCompApp_hom])
  -- the points of `X` over `ȳ` are the `v̄ ≫ ι_s ≫ fst`
  have hP : Nonempty P := ⟨eP.inv (IsLocalRing.closedPoint Ω)⟩
  have hinj (s t : S) (h : (v ≫ Sigma.ι (fun _ : S ↦ U) s) ≫ fst =
      (v ≫ Sigma.ι (fun _ : S ↦ U) t) ≫ fst) : s = t := by
    by_contra hst
    have h' : v ≫ Sigma.ι (fun _ : S ↦ U) s = v ≫ Sigma.ι (fun _ : S ↦ U) t :=
      hpb'.hom_ext (by simpa only [Category.assoc] using h) ((h4s s).trans (h4s t).symm)
    have := Scheme.isEmpty_of_isColimit_cofan (coproductIsCoproduct fun _ : S ↦ U) hst v v h'
    exact (this.false hP.some).elim
  have hex (x : FibrePoints f y) : ∃ s : S, (v ≫ Sigma.ι (fun _ : S ↦ U) s) ≫ fst = x.1 := by
    obtain ⟨x', hx'1, hx'2⟩ : ∃ x' : P ⟶ ∐ fun _ : S ↦ U, x' ≫ fst = x.1 ∧ x' ≫ fold = v :=
      ⟨hpb'.lift x.1 v (x.2.trans hv.symm), hpb'.lift_fst _ _ _, hpb'.lift_snd _ _ _⟩
    obtain ⟨s, hs⟩ := Scheme.exists_mem_range_of_isColimit_cofan
      (coproductIsCoproduct fun _ : S ↦ U) (x' (eP.inv (IsLocalRing.closedPoint Ω)))
    obtain ⟨w, hw⟩ := Scheme.exists_comp_eq_of_mem_range (Sigma.ι (fun _ : S ↦ U) s)
      (eP.inv ≫ x') (by simpa using hs)
    have hw' : (eP.hom ≫ w) ≫ Sigma.ι (fun _ : S ↦ U) s = x' := by
      rw [Category.assoc, hw, Iso.hom_inv_id_assoc]
    have hwv : eP.hom ≫ w = v := by
      rw [← hx'2, ← hw', Category.assoc, hι, Category.comp_id]
    exact ⟨s, by rw [← hwv, hw', hx'1]⟩
  choose σ hσ using hex
  have hσ' : Function.Bijective σ := by
    refine ⟨fun x x' h ↦ Subtype.ext ?_, fun s ↦ ⟨⟨(v ≫ Sigma.ι (fun _ : S ↦ U) s) ≫ fst, ?_⟩, ?_⟩⟩
    · rw [← hσ x, ← hσ x', h]
    · rw [Category.assoc, hpb'.w, ← Category.assoc, h4s, hv]
    · exact hinj _ _ (hσ _)
  -- the stalk of `f_* F` at `ȳ` through base change along `g`
  have hxy (s : S) : ((v ≫ Sigma.ι (fun _ : S ↦ U) s) ≫ fst) ≫ f = v ≫ g := by
    rw [Category.assoc, hpb'.w, ← Category.assoc, h4s]
  refine ⟨Fan.isLimitOfBijectiveIso σ hσ' h4 _
    ((upperStarCongr Λ hv.symm).app _ ≪≫ (upperStarComp Λ v g).app _ ≪≫
      (v)^*⟦Λ⟧.mapIso (asIso ((lowerStarBaseChange Λ hpb'.toCommSq).app F)))
    (fun x ↦ upperStarCompApp Λ (v ≫ Sigma.ι (fun _ : S ↦ U) (σ x)) fst F ≪≫
      (upperStarCongr Λ (hσ x)).app F) fun x ↦ ?_⟩
  have hh : ((v ≫ Sigma.ι (fun _ : S ↦ U) (σ x)) ≫ fst) ≫ f = y := by rw [hσ x]; exact x.2
  have h₁ := stalkLowerStarProj_lowerStarBaseChange' Λ hpb'.toCommSq (h4s (σ x)) (hxy (σ x)) F
  have h₂ :=
    (upperStarCongr_hom_app_stalkLowerStarProj Λ hv.symm hh (hxy (σ x)) F)
  have h₃ := stalkLowerStarProj_upperStarCongr_hom_app Λ (hσ x) hh x.2 F
  have h₁' : ((upperStarComp Λ v g).app ((f)_*⟦Λ⟧.obj F)).hom ≫
      ((v)^*⟦Λ⟧.mapIso (asIso ((lowerStarBaseChange Λ hpb'.toCommSq).app F))).hom ≫
      stalkLowerStarProj Λ (h4s (σ x)) N =
      stalkLowerStarProj Λ (hxy (σ x)) F ≫
        (upperStarCompApp Λ (v ≫ Sigma.ι (fun _ : S ↦ U) (σ x)) fst F).inv := h₁
  rw [← Iso.app_hom] at h₂ h₃
  exact Iso.eq_trans_hom_comp_trans_hom ((upperStarCongr Λ hv.symm).app _)
    ((upperStarComp Λ v g).app _)
    ((v)^*⟦Λ⟧.mapIso (asIso ((lowerStarBaseChange Λ hpb'.toCommSq).app F)))
    (stalkLowerStarProj Λ (h4s (σ x)) N)
    (upperStarCompApp Λ (v ≫ Sigma.ι (fun _ : S ↦ U) (σ x)) fst F)
    ((upperStarCongr Λ (hσ x)).app F) (stalkLowerStarProj Λ (hxy (σ x)) F) h₁' h₂ h₃

end AlgebraicGeometry.ProEtale.CondensedRing
