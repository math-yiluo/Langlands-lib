/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-!

# Coherence of the pullback exchanges of nearby cycles

The pullback exchanges `α_φ : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of morphisms of models
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange`) are
compatible with commutative squares of morphisms of models (blueprint
`sec-Base-change-for-nearby-cycles` (2), `α_{gf} = α_f(g^*) f_s^* α_g`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']

/-- The counit identity of the exchange morphism `exchangeRight af af' θ : Rf ⋙ G ⟶ G' ⋙ Rf'`. -/
lemma exchangeRight_app_comp_counit {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    (K : A) :
    Lf'.map ((exchangeRight af af' θ).app K) ≫ af'.counit.app (G'.obj K) =
      θ.hom.app (Rf.obj K) ≫ G'.map (af.counit.app K) := by
  simp [exchangeRight_app]

/-- `exchangeRight_app_comp_counit` for a transformation `bc` equal to the exchange morphism. -/
lemma exchangeRight_app_comp_counit' {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    (bc : Rf ⋙ G ⟶ G' ⋙ Rf') (h : bc = exchangeRight af af' θ) (K : A) :
    Lf'.map (bc.app K) ≫ af'.counit.app (G'.obj K) =
      θ.hom.app (Rf.obj K) ≫ G'.map (af.counit.app K) := by
  subst h
  exact exchangeRight_app_comp_counit af af' θ K

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Abstract computations -/

section Abstract

variable {DX1 DX DZ1 DZ TM1 TM TP1 TP GM1 GM GP1 GP : Type*} [Category DX1] [Category DX]
  [Category DZ1] [Category DZ] [Category TM1] [Category TM] [Category TP1] [Category TP]
  [Category GM1] [Category GM] [Category GP1] [Category GP]
  {g : DX1 ⥤ DX} {f : DX ⥤ DZ} {e : DX1 ⥤ DZ1} {k : DZ1 ⥤ DZ}
  {tψ : TM1 ⥤ TM} {tφ : TM ⥤ TP} {tφ' : TM1 ⥤ TP1} {tψ' : TP1 ⥤ TP}
  {gψ : GM1 ⥤ GM} {gφ : GM ⥤ GP} {gφ' : GM1 ⥤ GP1} {gψ' : GP1 ⥤ GP}
  {εM1 : DX1 ⥤ GM1} {εM : DX ⥤ GM} {εP1 : DZ1 ⥤ GP1} {εP : DZ ⥤ GP}
  {jM1 : TM1 ⥤ GM1} {jM : TM ⥤ GM} {jP1 : TP1 ⥤ GP1} {jP : TP ⥤ GP}
  {RM1 : GM1 ⥤ TM1} {RM : GM ⥤ TM} {RP1 : GP1 ⥤ TP1} {RP : GP ⥤ TP}

/-- The square law of the exchanges `t^* Rj_* ε^* ⟶ Rj_* ε^* f^*` of the total spaces, in abstract
categories: both sides have the same adjoint for `j_P^* ⊣ Rj_{P*}`, by the cubes of comparisons
of the `j`-squares and of the `ε`-squares. -/
lemma exchange_square_total_aux (aM1 : jM1 ⊣ RM1) (aM : jM ⊣ RM) (aP1 : jP1 ⊣ RP1)
    (aP : jP ⊣ RP)
    (cEψ : εM1 ⋙ gψ ⟶ g ⋙ εM) (cEφ : εM ⋙ gφ ⟶ f ⋙ εP) (cEφ' : εM1 ⋙ gφ' ⟶ e ⋙ εP1)
    (cEψ' : εP1 ⋙ gψ' ⟶ k ⋙ εP)
    (cJψ : tψ ⋙ jM ⟶ jM1 ⋙ gψ) (cJφ : tφ ⋙ jP ⟶ jM ⋙ gφ) (cJφ' : tφ' ⋙ jP1 ⟶ jM1 ⋙ gφ')
    (cJψ' : tψ' ⋙ jP ⟶ jP1 ⋙ gψ')
    (bψ : RM1 ⋙ tψ ⟶ gψ ⋙ RM) (bφ : RM ⋙ tφ ⟶ gφ ⋙ RP) (bφ' : RM1 ⋙ tφ' ⟶ gφ' ⋙ RP1)
    (bψ' : RP1 ⋙ tψ' ⟶ gψ' ⋙ RP)
    (hbψ : ∀ D, jM.map (bψ.app D) ≫ aM.counit.app _ = cJψ.app _ ≫ gψ.map (aM1.counit.app D))
    (hbφ : ∀ D, jP.map (bφ.app D) ≫ aP.counit.app _ = cJφ.app _ ≫ gφ.map (aM.counit.app D))
    (hbφ' : ∀ D, jP1.map (bφ'.app D) ≫ aP1.counit.app _ = cJφ'.app _ ≫ gφ'.map (aM1.counit.app D))
    (hbψ' : ∀ D, jP.map (bψ'.app D) ≫ aP.counit.app _ = cJψ'.app _ ≫ gψ'.map (aP1.counit.app D))
    (cT : tφ' ⋙ tψ' ⟶ tψ ⋙ tφ) (cG : gφ' ⋙ gψ' ⟶ gψ ⋙ gφ) (cB : e ⋙ k ⟶ g ⋙ f)
    (hJ : ∀ K, jP.map (cT.app K) ≫ cJφ.app (tψ.obj K) ≫ gφ.map (cJψ.app K) =
      cJψ'.app (tφ'.obj K) ≫ gψ'.map (cJφ'.app K) ≫ cG.app (jM1.obj K))
    (hE : ∀ C, cG.app (εM1.obj C) ≫ gφ.map (cEψ.app C) ≫ cEφ.app (g.obj C) =
      gψ'.map (cEφ'.app C) ≫ cEψ'.app (e.obj C) ≫ εP.map (cB.app C))
    (C : DX1) :
    cT.app (RM1.obj (εM1.obj C)) ≫ tφ.map (bψ.app (εM1.obj C) ≫ RM.map (cEψ.app C)) ≫
        bφ.app (εM.obj (g.obj C)) ≫ RP.map (cEφ.app (g.obj C)) =
      tψ'.map (bφ'.app (εM1.obj C) ≫ RP1.map (cEφ'.app C)) ≫ bψ'.app (εP1.obj (e.obj C)) ≫
        RP.map (cEψ'.app (e.obj C)) ≫ RP.map (εP.map (cB.app C)) := by
  apply (aP.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality, Adjunction.counit_naturality_assoc]
  have h₁ := hbφ (εM.obj (g.obj C))
  have h₂ := hbψ' (εP1.obj (e.obj C))
  simp only [Functor.comp_obj] at h₁ h₂
  rw [reassoc_of% h₁, reassoc_of% h₂]
  have h₃ := cJφ.naturality (bψ.app (εM1.obj C))
  have h₄ := cJφ.naturality (RM.map (cEψ.app C))
  have h₅ := cJψ'.naturality (bφ'.app (εM1.obj C))
  have h₆ := cJψ'.naturality (RP1.map (cEφ'.app C))
  simp only [Functor.comp_obj, Functor.comp_map] at h₃ h₄ h₅ h₆
  rw [reassoc_of% h₄, reassoc_of% h₃, reassoc_of% h₆, reassoc_of% h₅]
  simp only [← Functor.map_comp_assoc]
  have h₇ : jM.map (bψ.app (εM1.obj C) ≫ RM.map (cEψ.app C)) ≫ aM.counit.app (εM.obj (g.obj C)) =
      cJψ.app _ ≫ gψ.map (aM1.counit.app _) ≫ cEψ.app C := by
    have := aM.counit.naturality (cEψ.app C)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at this
    rw [Functor.map_comp, Category.assoc, this, ← Category.assoc, hbψ, Category.assoc]
  have h₈ : jP1.map (bφ'.app (εM1.obj C) ≫ RP1.map (cEφ'.app C)) ≫
      aP1.counit.app (εP1.obj (e.obj C)) =
      cJφ'.app _ ≫ gφ'.map (aM1.counit.app _) ≫ cEφ'.app C := by
    have := aP1.counit.naturality (cEφ'.app C)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at this
    rw [Functor.map_comp, Category.assoc, this, ← Category.assoc, hbφ', Category.assoc]
  rw [h₇, h₈]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hJ (RM1.obj (εM1.obj C)))]
  have h₉ := cG.naturality (aM1.counit.app (εM1.obj C))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h₉
  rw [← reassoc_of% h₉, hE C]

/-- The square law of the pullback exchanges `α = cI ≫ i_P^* β` of nearby cycles, in abstract
categories, from the cube of comparisons of the `i`-squares and the square law of the exchanges
`β` of the total spaces. -/
lemma exchange_square_aux {SM1 SM SP1 SP : Type*} [Category SM1] [Category SM] [Category SP1]
    [Category SP] {e' : SM1 ⥤ SP1} {k' : SP1 ⥤ SP} {g' : SM1 ⥤ SM} {f' : SM ⥤ SP}
    {iM1 : TM1 ⥤ SM1} {iM : TM ⥤ SM} {iP1 : TP1 ⥤ SP1} {iP : TP ⥤ SP}
    {ΦM1 : DX1 ⥤ TM1} {ΦM : DX ⥤ TM} {ΦP1 : DZ1 ⥤ TP1} {ΦP : DZ ⥤ TP}
    (cIψ : iM1 ⋙ g' ⟶ tψ ⋙ iM) (cIφ : iM ⋙ f' ⟶ tφ ⋙ iP) (cIφ' : iM1 ⋙ e' ⟶ tφ' ⋙ iP1)
    (cIψ' : iP1 ⋙ k' ⟶ tψ' ⋙ iP) (cS : e' ⋙ k' ⟶ g' ⋙ f') (cT : tφ' ⋙ tψ' ⟶ tψ ⋙ tφ)
    (cB : e ⋙ k ⟶ g ⋙ f)
    (hI : ∀ K, cS.app (iM1.obj K) ≫ f'.map (cIψ.app K) ≫ cIφ.app (tψ.obj K) =
      k'.map (cIφ'.app K) ≫ cIψ'.app (tφ'.obj K) ≫ iP.map (cT.app K))
    (C : DX1) (βψ : tψ.obj (ΦM1.obj C) ⟶ ΦM.obj (g.obj C))
    (βφ : tφ.obj (ΦM.obj (g.obj C)) ⟶ ΦP.obj (f.obj (g.obj C)))
    (βφ' : tφ'.obj (ΦM1.obj C) ⟶ ΦP1.obj (e.obj C))
    (βψ' : tψ'.obj (ΦP1.obj (e.obj C)) ⟶ ΦP.obj (k.obj (e.obj C)))
    (hβ : cT.app (ΦM1.obj C) ≫ tφ.map βψ ≫ βφ = tψ'.map βφ' ≫ βψ' ≫ ΦP.map (cB.app C)) :
    cS.app (iM1.obj (ΦM1.obj C)) ≫ f'.map (cIψ.app (ΦM1.obj C) ≫ iM.map βψ) ≫
        cIφ.app (ΦM.obj (g.obj C)) ≫ iP.map βφ =
      k'.map (cIφ'.app (ΦM1.obj C) ≫ iP1.map βφ') ≫ cIψ'.app (ΦP1.obj (e.obj C)) ≫
        iP.map βψ' ≫ iP.map (ΦP.map (cB.app C)) := by
  have h₁ := cIφ.naturality βψ
  have h₂ := cIψ'.naturality βφ'
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% (hI (ΦM1.obj C)), ← iP.map_comp,
    ← iP.map_comp, ← iP.map_comp, ← iP.map_comp, hβ]

/-- The square law of the pullback exchanges of nearby cycles, in abstract categories, with the
four pullback exchanges as variables characterized by their definitions and the nearby cycles as
the composites `ε ⋙ R ⋙ i`. -/
lemma pullbackExchange_square_aux {SM1 SM SP1 SP : Type*} [Category SM1] [Category SM]
    [Category SP1] [Category SP] {e' : SM1 ⥤ SP1} {k' : SP1 ⥤ SP} {g' : SM1 ⥤ SM}
    {f' : SM ⥤ SP} {iM1 : TM1 ⥤ SM1} {iM : TM ⥤ SM} {iP1 : TP1 ⥤ SP1} {iP : TP ⥤ SP}
    (aM1 : jM1 ⊣ RM1) (aM : jM ⊣ RM) (aP1 : jP1 ⊣ RP1) (aP : jP ⊣ RP)
    (cEψ : εM1 ⋙ gψ ⟶ g ⋙ εM) (cEφ : εM ⋙ gφ ⟶ f ⋙ εP) (cEφ' : εM1 ⋙ gφ' ⟶ e ⋙ εP1)
    (cEψ' : εP1 ⋙ gψ' ⟶ k ⋙ εP)
    (cJψ : tψ ⋙ jM ⟶ jM1 ⋙ gψ) (cJφ : tφ ⋙ jP ⟶ jM ⋙ gφ) (cJφ' : tφ' ⋙ jP1 ⟶ jM1 ⋙ gφ')
    (cJψ' : tψ' ⋙ jP ⟶ jP1 ⋙ gψ')
    (cIψ : iM1 ⋙ g' ⟶ tψ ⋙ iM) (cIφ : iM ⋙ f' ⟶ tφ ⋙ iP) (cIφ' : iM1 ⋙ e' ⟶ tφ' ⋙ iP1)
    (cIψ' : iP1 ⋙ k' ⟶ tψ' ⋙ iP) (cS : e' ⋙ k' ⟶ g' ⋙ f')
    (cT : tφ' ⋙ tψ' ⟶ tψ ⋙ tφ) (cG : gφ' ⋙ gψ' ⟶ gψ ⋙ gφ) (cB : e ⋙ k ⟶ g ⋙ f)
    (hI : ∀ K, cS.app (iM1.obj K) ≫ f'.map (cIψ.app K) ≫ cIφ.app (tψ.obj K) =
      k'.map (cIφ'.app K) ≫ cIψ'.app (tφ'.obj K) ≫ iP.map (cT.app K))
    (hJ : ∀ K, jP.map (cT.app K) ≫ cJφ.app (tψ.obj K) ≫ gφ.map (cJψ.app K) =
      cJψ'.app (tφ'.obj K) ≫ gψ'.map (cJφ'.app K) ≫ cG.app (jM1.obj K))
    (hE : ∀ C, cG.app (εM1.obj C) ≫ gφ.map (cEψ.app C) ≫ cEφ.app (g.obj C) =
      gψ'.map (cEφ'.app C) ≫ cEψ'.app (e.obj C) ≫ εP.map (cB.app C))
    (αψ : (εM1 ⋙ RM1 ⋙ iM1) ⋙ g' ⟶ g ⋙ εM ⋙ RM ⋙ iM)
    (hαψ : αψ = Functor.whiskerLeft (εM1 ⋙ RM1) cIψ ≫ Functor.whiskerRight
      (Functor.whiskerLeft εM1 (mateEquiv aM1 aM cJψ) ≫
        Functor.whiskerRight cEψ RM) iM)
    (αφ : (εM ⋙ RM ⋙ iM) ⋙ f' ⟶ f ⋙ εP ⋙ RP ⋙ iP)
    (hαφ : αφ = Functor.whiskerLeft (εM ⋙ RM) cIφ ≫ Functor.whiskerRight
      (Functor.whiskerLeft εM (mateEquiv aM aP cJφ) ≫
        Functor.whiskerRight cEφ RP) iP)
    (αφ' : (εM1 ⋙ RM1 ⋙ iM1) ⋙ e' ⟶ e ⋙ εP1 ⋙ RP1 ⋙ iP1)
    (hαφ' : αφ' = Functor.whiskerLeft (εM1 ⋙ RM1) cIφ' ≫ Functor.whiskerRight
      (Functor.whiskerLeft εM1 (mateEquiv aM1 aP1 cJφ') ≫
        Functor.whiskerRight cEφ' RP1) iP1)
    (αψ' : (εP1 ⋙ RP1 ⋙ iP1) ⋙ k' ⟶ k ⋙ εP ⋙ RP ⋙ iP)
    (hαψ' : αψ' = Functor.whiskerLeft (εP1 ⋙ RP1) cIψ' ≫ Functor.whiskerRight
      (Functor.whiskerLeft εP1 (mateEquiv aP1 aP cJψ') ≫
        Functor.whiskerRight cEψ' RP) iP)
    (C : DX1) :
    cS.app ((εM1 ⋙ RM1 ⋙ iM1).obj C) ≫ f'.map (αψ.app C) ≫ αφ.app (g.obj C) =
      k'.map (αφ'.app C) ≫ αψ'.app (e.obj C) ≫ (εP ⋙ RP ⋙ iP).map (cB.app C) := by
  subst hαψ hαφ hαφ' hαψ'
  have h := exchange_square_aux (ΦM1 := εM1 ⋙ RM1) (ΦM := εM ⋙ RM) (ΦP1 := εP1 ⋙ RP1)
    (ΦP := εP ⋙ RP) cIψ cIφ cIφ' cIψ' cS cT cB hI C
    ((mateEquiv aM1 aM cJψ).app (εM1.obj C) ≫ RM.map (cEψ.app C))
    ((mateEquiv aM aP cJφ).app (εM.obj (g.obj C)) ≫ RP.map (cEφ.app (g.obj C)))
    ((mateEquiv aM1 aP1 cJφ').app (εM1.obj C) ≫ RP1.map (cEφ'.app C))
    ((mateEquiv aP1 aP cJψ').app (εP1.obj (e.obj C)) ≫ RP.map (cEψ'.app (e.obj C)))
    (by
      have := exchange_square_total_aux aM1 aM aP1 aP cEψ cEφ cEφ' cEψ' cJψ cJφ cJφ' cJψ'
        _ _ _ _ (fun D ↦ mateEquiv_counit _ _ _ D) (fun D ↦ mateEquiv_counit _ _ _ D)
        (fun D ↦ mateEquiv_counit _ _ _ D) (fun D ↦ mateEquiv_counit _ _ _ D) cT cG cB hJ hE C
      simp only [Category.assoc, Functor.comp_map] at this ⊢
      exact this)
  simp only [Category.assoc, Functor.comp_map, Functor.map_comp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj] at h ⊢
  exact h

section Monoidal

variable {TN TM GN GM : Type*} [Category TN] [Category TM] [Category GN] [Category GM]
  [MonoidalCategory TN] [MonoidalCategory TM] [MonoidalCategory GN] [MonoidalCategory GM]
  {t : TN ⥤ TM} {gen : GN ⥤ GM} {jN : TN ⥤ GN} {jM : TM ⥤ GM} {RN : GN ⥤ TN} {RM : GM ⥤ TM}
  [t.OplaxMonoidal] [gen.OplaxMonoidal] [jN.OplaxMonoidal] [jM.OplaxMonoidal]

/-- The base change morphism `bc : t^* Rj_{N*} ⟶ Rj_{M*} gen^*` (with counit identity
`hbc`) is monoidal for the lax tensor maps of the pushforwards, the adjoints of the tensor
products of the counits, if the comparison `cJ : t^* j_M^* ⟶ gen^* j_N^*` is monoidal. -/
lemma baseChange_tensor_aux (aN : jN ⊣ RN) (aM : jM ⊣ RM) (cJ : t ⋙ jM ⟶ jN ⋙ gen)
    (bc : RN ⋙ t ⟶ gen ⋙ RM)
    (hbc : ∀ D, jM.map (bc.app D) ≫ aM.counit.app _ = cJ.app _ ≫ gen.map (aN.counit.app D))
    (hcJ : ∀ X Y, jM.map (Functor.OplaxMonoidal.δ t X Y) ≫ Functor.OplaxMonoidal.δ jM _ _ ≫
      (cJ.app X ⊗ₘ cJ.app Y) =
        cJ.app (X ⊗ Y) ≫ gen.map (Functor.OplaxMonoidal.δ jN X Y) ≫
          Functor.OplaxMonoidal.δ gen _ _)
    (U V : GN) :
    t.map (aN.homEquiv _ _ (Functor.OplaxMonoidal.δ jN _ _ ≫
        (aN.counit.app U ⊗ₘ aN.counit.app V))) ≫ bc.app (U ⊗ V) ≫
        RM.map (Functor.OplaxMonoidal.δ gen U V) =
      Functor.OplaxMonoidal.δ t (RN.obj U) (RN.obj V) ≫ (bc.app U ⊗ₘ bc.app V) ≫
        aM.homEquiv _ _ (Functor.OplaxMonoidal.δ jM _ _ ≫
          (aM.counit.app (gen.obj U) ⊗ₘ aM.counit.app (gen.obj V))) := by
  have hμN : jN.map (aN.homEquiv _ _ (Functor.OplaxMonoidal.δ jN _ _ ≫
      (aN.counit.app U ⊗ₘ aN.counit.app V))) ≫ aN.counit.app _ =
      Functor.OplaxMonoidal.δ jN _ _ ≫ (aN.counit.app U ⊗ₘ aN.counit.app V) := by
    erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  have hμM : jM.map (aM.homEquiv _ _ (Functor.OplaxMonoidal.δ jM _ _ ≫
      (aM.counit.app (gen.obj U) ⊗ₘ aM.counit.app (gen.obj V)))) ≫ aM.counit.app _ =
      Functor.OplaxMonoidal.δ jM _ _ ≫
        (aM.counit.app (gen.obj U) ⊗ₘ aM.counit.app (gen.obj V)) := by
    erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  have hδ := aM.counit.naturality (Functor.OplaxMonoidal.δ gen U V)
  have hn := cJ.naturality (aN.homEquiv _ _ (Functor.OplaxMonoidal.δ jN _ _ ≫
      (aN.counit.app U ⊗ₘ aN.counit.app V)))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hδ hn
  apply (aM.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  erw [hδ, reassoc_of% (hbc (U ⊗ V)), reassoc_of% hn, ← gen.map_comp_assoc, hμN, hμM,
    ← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom, hbc U, hbc V,
    ← tensorHom_comp_tensorHom, reassoc_of% (hcJ _ _), gen.map_comp_assoc,
    Functor.OplaxMonoidal.δ_natural]
  rfl

/-- The pullback exchange `α = cI ≫ i_M^* (bc ≫ Rj_{M*} cE)` is monoidal for the lax tensor maps
`μ_Ψ = μ_i ≫ i^* (μ_j ≫ Rj_* μ_ε)` of nearby cycles, in abstract categories, if the comparisons
`cI`, `cE` and the base change morphism `bc` are monoidal. -/
lemma pullbackExchange_tensor_aux {SN SM DY DX : Type*} [Category SN] [Category SM] [Category DY]
    [Category DX] [MonoidalCategory SN] [MonoidalCategory SM] [MonoidalCategory DY]
    [MonoidalCategory DX] {f' : SN ⥤ SM} {iN : TN ⥤ SN} {iM : TM ⥤ SM} {f : DY ⥤ DX}
    {εN : DY ⥤ GN} {εM : DX ⥤ GM} [f'.OplaxMonoidal] [iN.Monoidal] [iM.Monoidal]
    [f.OplaxMonoidal] [εN.Monoidal] [εM.Monoidal]
    (cI : iN ⋙ f' ⟶ t ⋙ iM) (cE : εN ⋙ gen ⟶ f ⋙ εM) (bc : RN ⋙ t ⟶ gen ⋙ RM)
    (μjN : ∀ U V : GN, RN.obj U ⊗ RN.obj V ⟶ RN.obj (U ⊗ V))
    (μjM : ∀ U V : GM, RM.obj U ⊗ RM.obj V ⟶ RM.obj (U ⊗ V))
    (hμjM : ∀ {U U' V V' : GM} (x : U ⟶ U') (y : V ⟶ V'),
      (RM.map x ⊗ₘ RM.map y) ≫ μjM U' V' = μjM U V ≫ RM.map (x ⊗ₘ y))
    (hcI : ∀ X Y, f'.map (Functor.OplaxMonoidal.δ iN X Y) ≫ Functor.OplaxMonoidal.δ f' _ _ ≫
      (cI.app X ⊗ₘ cI.app Y) =
        cI.app (X ⊗ Y) ≫ iM.map (Functor.OplaxMonoidal.δ t X Y) ≫
          Functor.OplaxMonoidal.δ iM _ _)
    (hcE : ∀ A B, gen.map (Functor.OplaxMonoidal.δ εN A B) ≫ Functor.OplaxMonoidal.δ gen _ _ ≫
      (cE.app A ⊗ₘ cE.app B) =
        cE.app (A ⊗ B) ≫ εM.map (Functor.OplaxMonoidal.δ f A B) ≫
          Functor.OplaxMonoidal.δ εM _ _)
    (hbc : ∀ U V, t.map (μjN U V) ≫ bc.app (U ⊗ V) ≫ RM.map (Functor.OplaxMonoidal.δ gen U V) =
      Functor.OplaxMonoidal.δ t (RN.obj U) (RN.obj V) ≫ (bc.app U ⊗ₘ bc.app V) ≫
        μjM (gen.obj U) (gen.obj V))
    (A B : DY) :
    f'.map (Functor.LaxMonoidal.μ iN (RN.obj (εN.obj A)) (RN.obj (εN.obj B)) ≫
        iN.map (μjN (εN.obj A) (εN.obj B) ≫ RN.map (Functor.LaxMonoidal.μ εN A B))) ≫
        (cI.app (RN.obj (εN.obj (A ⊗ B))) ≫
          iM.map (bc.app (εN.obj (A ⊗ B)) ≫ RM.map (cE.app (A ⊗ B)))) ≫
        iM.map (RM.map (εM.map (Functor.OplaxMonoidal.δ f A B))) =
      Functor.OplaxMonoidal.δ f' _ _ ≫
        ((cI.app (RN.obj (εN.obj A)) ≫ iM.map (bc.app (εN.obj A) ≫ RM.map (cE.app A))) ⊗ₘ
          (cI.app (RN.obj (εN.obj B)) ≫ iM.map (bc.app (εN.obj B) ≫ RM.map (cE.app B)))) ≫
        Functor.LaxMonoidal.μ iM (RM.obj (εM.obj (f.obj A))) (RM.obj (εM.obj (f.obj B))) ≫
          iM.map (μjM (εM.obj (f.obj A)) (εM.obj (f.obj B)) ≫
            RM.map (Functor.LaxMonoidal.μ εM (f.obj A) (f.obj B))) := by
  -- the monoidality of `cE` in the form needed
  have hE : gen.map (Functor.LaxMonoidal.μ εN A B) ≫ cE.app (A ⊗ B) ≫
      εM.map (Functor.OplaxMonoidal.δ f A B) =
      Functor.OplaxMonoidal.δ gen _ _ ≫ (cE.app A ⊗ₘ cE.app B) ≫
        Functor.LaxMonoidal.μ εM _ _ := by
    rw [← cancel_epi (gen.map (Functor.OplaxMonoidal.δ εN A B)), ← gen.map_comp_assoc,
      Functor.Monoidal.δ_μ, gen.map_id, Category.id_comp, reassoc_of% (hcE A B),
      Functor.Monoidal.δ_μ, Category.comp_id]
  -- the monoidality of `cI` in the form needed
  have hI : f'.map (Functor.LaxMonoidal.μ iN (RN.obj (εN.obj A)) (RN.obj (εN.obj B))) ≫
      cI.app _ ≫ iM.map (Functor.OplaxMonoidal.δ t _ _) =
      Functor.OplaxMonoidal.δ f' _ _ ≫ (cI.app _ ⊗ₘ cI.app _) ≫
        Functor.LaxMonoidal.μ iM _ _ := by
    rw [← cancel_epi (f'.map (Functor.OplaxMonoidal.δ iN _ _)), ← f'.map_comp_assoc,
      Functor.Monoidal.δ_μ, f'.map_id, Category.id_comp, reassoc_of% (hcI _ _),
      Functor.Monoidal.δ_μ, Category.comp_id]
  have h₁ := cI.naturality (μjN (εN.obj A) (εN.obj B) ≫ RN.map (Functor.LaxMonoidal.μ εN A B))
  have h₂ := bc.naturality (Functor.LaxMonoidal.μ εN A B)
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  have hin : t.map (μjN (εN.obj A) (εN.obj B) ≫ RN.map (Functor.LaxMonoidal.μ εN A B)) ≫
      (bc.app (εN.obj (A ⊗ B)) ≫ RM.map (cE.app (A ⊗ B))) ≫
        RM.map (εM.map (Functor.OplaxMonoidal.δ f A B)) =
      Functor.OplaxMonoidal.δ t _ _ ≫
        ((bc.app (εN.obj A) ≫ RM.map (cE.app A)) ⊗ₘ (bc.app (εN.obj B) ≫ RM.map (cE.app B))) ≫
        μjM (εM.obj (f.obj A)) (εM.obj (f.obj B)) ≫
          RM.map (Functor.LaxMonoidal.μ εM (f.obj A) (f.obj B)) := by
    have hE' : RM.map (gen.map (Functor.LaxMonoidal.μ εN A B)) ≫ RM.map (cE.app (A ⊗ B)) ≫
        RM.map (εM.map (Functor.OplaxMonoidal.δ f A B)) =
        RM.map (Functor.OplaxMonoidal.δ gen _ _) ≫ RM.map (cE.app A ⊗ₘ cE.app B) ≫
          RM.map (Functor.LaxMonoidal.μ εM _ _) := by
      rw [← RM.map_comp, ← RM.map_comp, hE, RM.map_comp, RM.map_comp]
    simp only [t.map_comp, Category.assoc]
    rw [reassoc_of% h₂, hE', reassoc_of% (hbc _ _), ← reassoc_of% (hμjM (cE.app A) (cE.app B)),
      ← tensorHom_comp_tensorHom_assoc]
  rw [f'.map_comp, Category.assoc, Category.assoc, reassoc_of% h₁, ← iM.map_comp,
    ← iM.map_comp, hin, iM.map_comp, reassoc_of% hI]
  simp only [← tensorHom_comp_tensorHom, Category.assoc, iM.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_assoc, ← Functor.LaxMonoidal.μ_natural_assoc]
  rfl

/-- `pullbackExchange_tensor_aux` with the pullback exchange `α` and the lax tensor maps `μ_N`,
`μ_M` of nearby cycles as variables characterized by their definitions, and the nearby cycles
as the composites `ε ⋙ R ⋙ i`. -/
lemma pullbackExchange_tensor_aux' {SN SM DY DX : Type*} [Category SN] [Category SM]
    [Category DY] [Category DX] [MonoidalCategory SN] [MonoidalCategory SM]
    [MonoidalCategory DY] [MonoidalCategory DX] {f' : SN ⥤ SM} {iN : TN ⥤ SN} {iM : TM ⥤ SM}
    {f : DY ⥤ DX} {εN : DY ⥤ GN} {εM : DX ⥤ GM} [f'.OplaxMonoidal] [iN.Monoidal] [iM.Monoidal]
    [f.OplaxMonoidal] [εN.Monoidal] [εM.Monoidal]
    (cI : iN ⋙ f' ⟶ t ⋙ iM) (cE : εN ⋙ gen ⟶ f ⋙ εM) (bc : RN ⋙ t ⟶ gen ⋙ RM)
    (μjN : ∀ U V : GN, RN.obj U ⊗ RN.obj V ⟶ RN.obj (U ⊗ V))
    (μjM : ∀ U V : GM, RM.obj U ⊗ RM.obj V ⟶ RM.obj (U ⊗ V))
    (hμjM : ∀ {U U' V V' : GM} (x : U ⟶ U') (y : V ⟶ V'),
      (RM.map x ⊗ₘ RM.map y) ≫ μjM U' V' = μjM U V ≫ RM.map (x ⊗ₘ y))
    (hcI : ∀ X Y, f'.map (Functor.OplaxMonoidal.δ iN X Y) ≫ Functor.OplaxMonoidal.δ f' _ _ ≫
      (cI.app X ⊗ₘ cI.app Y) =
        cI.app (X ⊗ Y) ≫ iM.map (Functor.OplaxMonoidal.δ t X Y) ≫
          Functor.OplaxMonoidal.δ iM _ _)
    (hcE : ∀ A B, gen.map (Functor.OplaxMonoidal.δ εN A B) ≫ Functor.OplaxMonoidal.δ gen _ _ ≫
      (cE.app A ⊗ₘ cE.app B) =
        cE.app (A ⊗ B) ≫ εM.map (Functor.OplaxMonoidal.δ f A B) ≫
          Functor.OplaxMonoidal.δ εM _ _)
    (hbc : ∀ U V, t.map (μjN U V) ≫ bc.app (U ⊗ V) ≫ RM.map (Functor.OplaxMonoidal.δ gen U V) =
      Functor.OplaxMonoidal.δ t (RN.obj U) (RN.obj V) ≫ (bc.app U ⊗ₘ bc.app V) ≫
        μjM (gen.obj U) (gen.obj V))
    (α : (εN ⋙ RN ⋙ iN) ⋙ f' ⟶ f ⋙ εM ⋙ RM ⋙ iM)
    (hα : α = Functor.whiskerLeft (εN ⋙ RN) cI ≫
      Functor.whiskerRight (Functor.whiskerLeft εN bc ≫ Functor.whiskerRight cE RM) iM)
    (μN : ∀ A B, (εN ⋙ RN ⋙ iN).obj A ⊗ (εN ⋙ RN ⋙ iN).obj B ⟶ (εN ⋙ RN ⋙ iN).obj (A ⊗ B))
    (hμN : μN = fun A B ↦ Functor.LaxMonoidal.μ iN _ _ ≫
      iN.map (μjN _ _ ≫ RN.map (Functor.LaxMonoidal.μ εN A B)))
    (μM : ∀ A B, (εM ⋙ RM ⋙ iM).obj A ⊗ (εM ⋙ RM ⋙ iM).obj B ⟶ (εM ⋙ RM ⋙ iM).obj (A ⊗ B))
    (hμM : μM = fun A B ↦ Functor.LaxMonoidal.μ iM _ _ ≫
      iM.map (μjM _ _ ≫ RM.map (Functor.LaxMonoidal.μ εM A B)))
    (A B : DY) :
    f'.map (μN A B) ≫ α.app (A ⊗ B) ≫ (εM ⋙ RM ⋙ iM).map (Functor.OplaxMonoidal.δ f A B) =
      Functor.OplaxMonoidal.δ f' _ _ ≫ (α.app A ⊗ₘ α.app B) ≫ μM _ _ := by
  subst hα hμN hμM
  exact pullbackExchange_tensor_aux cI cE bc μjN μjM hμjM hcI hcE hbc A B

end Monoidal

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Exchange maps -/

namespace NearbyCyclesModel.Hom

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- **The pullback exchange is monoidal** (blueprint `sec-Base-change-for-nearby-cycles`, "`α_f`
is monoidal"): `α_φ(A ⊗ B) ∘ Lf'^* μ_N = Ψ_M(m⁻¹) ∘ μ_M ∘ (α_φ A ⊗ α_φ B) ∘ m`, where `μ` are
the lax tensor maps of nearby cycles and `m` the tensor comparisons of the derived pullbacks. -/
lemma map_tensorMap_comp_pullbackExchange_app
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((f')^*⟦Λ⟧).map (N.tensorMap Λ A B) ≫ (φ.pullbackExchange Λ).app (A ⊗ B) ≫
        (M.nearbyCycles Λ).map (Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) A B) =
      Functor.OplaxMonoidal.δ L((f')^*⟦Λ⟧) _ _ ≫
        ((φ.pullbackExchange Λ).app A ⊗ₘ (φ.pullbackExchange Λ).app B) ≫
          M.tensorMap Λ _ _ := by
  exact pullbackExchange_tensor_aux' (pullbackSquareComparison Λ φ.commSq_i).hom
    (pullbackSquareComparison Λ φ.commSq_ε).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    (lowerStarTensorMap' Λ N.j) (lowerStarTensorMap' Λ M.j)
    (fun x y ↦ lowerStarTensorMap'_natural Λ M.j x y)
    (fun X Y ↦ pullbackSquareComparison_tensor Λ φ.commSq_i X Y)
    (fun X Y ↦ pullbackSquareComparison_tensor Λ φ.commSq_ε X Y)
    (fun U V ↦ baseChange_tensor_aux (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j) (pullbackSquareComparison Λ φ.commSq_j).hom
      _ (fun D ↦ mateEquiv_counit _ _ _ D)
      (fun X Y ↦ pullbackSquareComparison_tensor Λ φ.commSq_j X Y) U V)
    (φ.pullbackExchange Λ) rfl (N.tensorMap Λ) rfl (M.tensorMap Λ) rfl A B

variable {Z Z' X₁ X₁' Z₁ Z₁' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P₁ : NearbyCyclesModel Z₁ Z₁'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'}
  {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'} {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'} {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'}

/-- **The square law of the pullback exchanges** (blueprint `sec-Base-change-for-nearby-cycles`
(2), `α_{gf} = α_f(g^*) f_s^* α_g`, for the two factorizations of a commutative square of
morphisms of models): for morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`, `ψ' : P ⟶ P₁` and
`φ₁ : P₁ ⟶ M₁` with `φ₀ ≫ ψ = ψ' ≫ φ₁`, the two composite pullback exchanges
`Lk'^* Le'^* Ψ_{M₁} ⟶ Ψ_P Lf₀^* Lg^*` agree, up to the comparisons of the squares of special
fibres and of bases. -/
lemma pullbackExchange_square (φ₀ : P.Hom M f₀ f₀') (ψ : M.Hom M₁ g g') (ψ' : P.Hom P₁ k k')
    (φ₁ : P₁.Hom M₁ e e') (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁))) :
    (pullbackSquareComparison Λ (⟨hs⟩ : CommSq f₀' k' g' e')).hom.app
        ((M₁.nearbyCycles Λ).obj C) ≫ L((f₀')^*⟦Λ⟧).map ((ψ.pullbackExchange Λ).app C) ≫
        (φ₀.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C) =
      L((k')^*⟦Λ⟧).map ((φ₁.pullbackExchange Λ).app C) ≫
        (ψ'.pullbackExchange Λ).app (L((e)^*⟦Λ⟧).obj C) ≫
        (P.nearbyCycles Λ).map
          ((pullbackSquareComparison Λ (⟨hb⟩ : CommSq f₀ k g e)).hom.app C) := by
  have h := pullbackExchange_square_aux (derivedUpperStarLowerStarAdjunction Λ M₁.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j) (derivedUpperStarLowerStarAdjunction Λ P₁.j)
    (derivedUpperStarLowerStarAdjunction Λ P.j)
    (pullbackSquareComparison Λ ψ.commSq_ε).hom (pullbackSquareComparison Λ φ₀.commSq_ε).hom
    (pullbackSquareComparison Λ φ₁.commSq_ε).hom (pullbackSquareComparison Λ ψ'.commSq_ε).hom
    (pullbackSquareComparison Λ ψ.commSq_j).hom (pullbackSquareComparison Λ φ₀.commSq_j).hom
    (pullbackSquareComparison Λ φ₁.commSq_j).hom (pullbackSquareComparison Λ ψ'.commSq_j).hom
    (pullbackSquareComparison Λ ψ.commSq_i).hom (pullbackSquareComparison Λ φ₀.commSq_i).hom
    (pullbackSquareComparison Λ φ₁.commSq_i).hom (pullbackSquareComparison Λ ψ'.commSq_i).hom
    (pullbackSquareComparison Λ (⟨hs⟩ : CommSq f₀' k' g' e')).hom
    (pullbackSquareComparison Λ (⟨htot⟩ : CommSq φ₀.total ψ'.total ψ.total φ₁.total)).hom
    (pullbackSquareComparison Λ
      (⟨hgen⟩ : CommSq φ₀.generic ψ'.generic ψ.generic φ₁.generic)).hom
    (pullbackSquareComparison Λ (⟨hb⟩ : CommSq f₀ k g e)).hom
    (fun K ↦ pullbackSquareComparison_cube Λ ⟨hs⟩ ⟨htot⟩ φ₀.commSq_i ψ.commSq_i
      ψ'.commSq_i φ₁.commSq_i K)
    (fun K ↦ (pullbackSquareComparison_cube Λ ψ'.commSq_j ψ.commSq_j ⟨hgen⟩ φ₁.commSq_j
      φ₀.commSq_j ⟨htot⟩ K).symm)
    (fun C ↦ pullbackSquareComparison_cube Λ ⟨hgen⟩ ⟨hb⟩ φ₀.commSq_ε ψ.commSq_ε
      ψ'.commSq_ε φ₁.commSq_ε C)
    (ψ.pullbackExchange Λ) rfl (φ₀.pullbackExchange Λ) rfl (φ₁.pullbackExchange Λ) rfl
    (ψ'.pullbackExchange Λ) rfl C
  convert h using 3 <;> rfl

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
