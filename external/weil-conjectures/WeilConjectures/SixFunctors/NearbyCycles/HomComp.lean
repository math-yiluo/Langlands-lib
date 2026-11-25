/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.CategoryTheory.Adjunction.MateCompose

/-!

# Composition of morphisms of models and the exchanges of nearby cycles

This file defines the composite of morphisms of models
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.comp`) and proves that both
exchanges of nearby cycles are compatible with composition (blueprint
`prose-E-03`).

## Main results

- `NearbyCyclesModel.Hom.pullbackExchange_comp_app`: for `φ : M ⟶ N` over `f` and `ψ : N ⟶ P`
  over `g`, `α_{φψ} = Ψ_M(c_{f,g}⁻¹) ∘ α_φ(Lg^*) ∘ Lf'^* α_ψ ∘ c_{f',g'}`, where
  `c : L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` are the composition isomorphisms of derived pullbacks.
- `NearbyCyclesModel.Hom.pushforwardExchange_comp_app`: the mates satisfy
  `χ_{φψ} = Rg'_*(χ_φ) ∘ χ_ψ(Rf_*)`, through the conjugate composition isomorphisms
  `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`.
- `NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`,
  `NearbyCyclesModel.Hom.pushforwardExchange_comp_app_of_eq`: the same laws for any morphism of
  models `χ` over factorizations `f ≫ g = fg`, `f' ≫ g' = fg'` whose components are the
  composites (e.g. over `(f ≫ g).left` for morphisms in `Over S`).
- `ProEtale.CondensedRing.pullbackSquareComparison_hom_app_paste`: the pullback comparison of a
  pasted square is the composite of the pullback comparisons of the two squares.
- `ProEtale.CondensedRing.boundedConstructibleLowerStarComp_inv_app_hom`: on the ambient derived
  category, the composition isomorphism of the pushforwards on bounded constructible complexes
  is the conjugate of the composition isomorphism of the derived pullbacks.

## Implementation notes

The diagram chases are carried out in abstract categories (the `_aux` lemmas) and then
instantiated. The composition isomorphisms are transported along equalities `p ≫ q = pq`
(`ProEtale.CondensedRing.leftDerivedUpperStarCompOfEq`): unifying `p ≫ q` with a definitionally
equal morphism such as `(φ.comp ψ).total` inside derived functors times out.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- The diagram chase behind `pullbackSquareComparison_hom_app_paste`. -/
private lemma paste_aux {C : Type*} [Category C] {x₀ x₁ x₂ x₃ x₄ y₀ y₁ z₀ z₁ w₀ w₁ : C}
    (A : x₀ ⟶ x₁) (A' : x₁ ⟶ x₀) (hA : A' ≫ A = 𝟙 _) (B : x₁ ⟶ x₂) (C₂ : x₂ ⟶ x₃)
    (D : x₃ ⟶ x₄) (E : x₁ ⟶ w₁) (F : w₁ ⟶ x₄) (U : y₀ ⟶ y₁) (V : y₁ ⟶ x₂) (U₂ : z₀ ⟶ z₁)
    (V₂ : z₁ ⟶ x₃) (U₃ : w₀ ⟶ w₁) (e₁ : x₀ = y₀) (e₂ : y₀ = z₀) (e₃ : z₀ = w₀) (e₄ : x₀ = w₀)
    (h₁ : A ≫ B = eqToHom e₁ ≫ U ≫ V) (h₂ : U ≫ V ≫ C₂ = eqToHom e₂ ≫ U₂ ≫ V₂)
    (h₃ : U₂ ≫ V₂ ≫ D = eqToHom e₃ ≫ U₃ ≫ F) (h₄ : E = A' ≫ eqToHom e₄ ≫ U₃) :
    B ≫ C₂ ≫ D = E ≫ F := by
  subst e₁ e₂ e₃ h₄
  simp only [eqToHom_refl, Category.id_comp] at h₁ h₂ h₃ ⊢
  rw [← Category.id_comp (B ≫ _), ← hA, Category.assoc, reassoc_of% h₁, reassoc_of% h₂, h₃,
    Category.assoc]

/-- The composition law of the pullback exchanges of nearby cycles, in abstract categories: the
case of `pullbackExchange_square_aux` in which one of the four morphisms is the identity. -/
lemma pullbackExchange_comp_aux {DP DN DM SP SN SM TP TN TM GP GN GM : Type*} [Category DP]
    [Category DN] [Category DM] [Category SP] [Category SN] [Category SM] [Category TP]
    [Category TN] [Category TM] [Category GP] [Category GN] [Category GM]
    {g : DP ⥤ DN} {f : DN ⥤ DM} {h : DP ⥤ DM} {g' : SP ⥤ SN} {f' : SN ⥤ SM} {h' : SP ⥤ SM}
    {tψ : TP ⥤ TN} {tφ : TN ⥤ TM} {tc : TP ⥤ TM} {gψ : GP ⥤ GN} {gφ : GN ⥤ GM} {gc : GP ⥤ GM}
    {εP : DP ⥤ GP} {εN : DN ⥤ GN} {εM : DM ⥤ GM} {jP : TP ⥤ GP} {jN : TN ⥤ GN} {jM : TM ⥤ GM}
    {RP : GP ⥤ TP} {RN : GN ⥤ TN} {RM : GM ⥤ TM} {iP : TP ⥤ SP} {iN : TN ⥤ SN} {iM : TM ⥤ SM}
    (aP : jP ⊣ RP) (aN : jN ⊣ RN) (aM : jM ⊣ RM)
    (cB : h ⟶ g ⋙ f) (cS : h' ⟶ g' ⋙ f') (cT : tc ⟶ tψ ⋙ tφ) (cG : gc ⟶ gψ ⋙ gφ)
    (cIψ : iP ⋙ g' ⟶ tψ ⋙ iN) (cIφ : iN ⋙ f' ⟶ tφ ⋙ iM) (cIc : iP ⋙ h' ⟶ tc ⋙ iM)
    (cJψ : tψ ⋙ jN ≅ jP ⋙ gψ) (cJφ : tφ ⋙ jM ≅ jN ⋙ gφ) (cJc : tc ⋙ jM ≅ jP ⋙ gc)
    (cEψ : εP ⋙ gψ ⟶ g ⋙ εN) (cEφ : εN ⋙ gφ ⟶ f ⋙ εM) (cEc : εP ⋙ gc ⟶ h ⋙ εM)
    (hI : ∀ K, cS.app (iP.obj K) ≫ f'.map (cIψ.app K) ≫ cIφ.app (tψ.obj K) =
      cIc.app K ≫ iM.map (cT.app K))
    (dψ : jP ⋙ gψ ⟶ tψ ⋙ jN) (hdψ : dψ = cJψ.inv) (dφ : jN ⋙ gφ ⟶ tφ ⋙ jM)
    (hdφ : dφ = cJφ.inv) (dc : jP ⋙ gc ⟶ tc ⋙ jM) (hdc : dc = cJc.inv)
    (hJ : ∀ K, cG.app (jP.obj K) ≫ gφ.map (dψ.app K) ≫ dφ.app (tψ.obj K) =
      dc.app K ≫ jM.map (cT.app K))
    (hE : ∀ C, cG.app (εP.obj C) ≫ gφ.map (cEψ.app C) ≫ cEφ.app (g.obj C) =
      cEc.app C ≫ εM.map (cB.app C))
    (αψ : (εP ⋙ RP ⋙ iP) ⋙ g' ⟶ g ⋙ εN ⋙ RN ⋙ iN)
    (hαψ : αψ = Functor.whiskerLeft (εP ⋙ RP) cIψ ≫ Functor.whiskerRight
      (Functor.whiskerLeft εP (mateEquiv aP aN cJψ.hom) ≫
        Functor.whiskerRight cEψ RN) iN)
    (αφ : (εN ⋙ RN ⋙ iN) ⋙ f' ⟶ f ⋙ εM ⋙ RM ⋙ iM)
    (hαφ : αφ = Functor.whiskerLeft (εN ⋙ RN) cIφ ≫ Functor.whiskerRight
      (Functor.whiskerLeft εN (mateEquiv aN aM cJφ.hom) ≫
        Functor.whiskerRight cEφ RM) iM)
    (αc : (εP ⋙ RP ⋙ iP) ⋙ h' ⟶ h ⋙ εM ⋙ RM ⋙ iM)
    (hαc : αc = Functor.whiskerLeft (εP ⋙ RP) cIc ≫ Functor.whiskerRight
      (Functor.whiskerLeft εP (mateEquiv aP aM cJc.hom) ≫
        Functor.whiskerRight cEc RM) iM)
    (C : DP) :
    cS.app ((εP ⋙ RP ⋙ iP).obj C) ≫ f'.map (αψ.app C) ≫ αφ.app (g.obj C) =
      αc.app C ≫ (εM ⋙ RM ⋙ iM).map (cB.app C) := by
  subst hdψ hdφ hdc
  have hJ' : ∀ K, jM.map (cT.app K) ≫ cJφ.hom.app (tψ.obj K) ≫ gφ.map (cJψ.hom.app K) =
      cJc.hom.app K ≫ cG.app (jP.obj K) := fun K ↦ by
    rw [← cancel_epi (cJc.inv.app K), ← reassoc_of% (hJ K)]
    simp [← Functor.map_comp]
  have h := pullbackExchange_square_aux (k := 𝟭 DM) (k' := 𝟭 SM) (tψ' := 𝟭 TM) (gψ' := 𝟭 GM)
    aP aN aM aM cEψ cEφ cEc ((Functor.rightUnitor εM).hom ≫ (Functor.leftUnitor εM).inv)
    cJψ.hom cJφ.hom cJc.hom ((Functor.leftUnitor jM).hom ≫ (Functor.rightUnitor jM).inv)
    cIψ cIφ cIc ((Functor.rightUnitor iM).hom ≫ (Functor.leftUnitor iM).inv)
    ((Functor.rightUnitor h').hom ≫ cS) ((Functor.rightUnitor tc).hom ≫ cT)
    ((Functor.rightUnitor gc).hom ≫ cG) ((Functor.rightUnitor h).hom ≫ cB)
    (fun K ↦ by simpa using hI K) (fun K ↦ by simpa using hJ' K)
    (fun C ↦ by simpa using hE C) αψ hαψ αφ hαφ αc hαc
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)
    (by
      ext X
      simp [mateEquiv_apply, ← Functor.map_comp]) C
  simpa using h

/-- `mateEquiv_app_comp_conjugateIsoEquiv_hom_app` with the mates as variables characterized by
their definitions. -/
lemma mateEquiv_comp_aux {A B C A' B' C' : Type*} [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : A ⥤ C} {R₃ : C ⥤ A}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'} {L₃' : A' ⥤ C'}
    {R₃' : C' ⥤ A'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₁' : L₁' ⊣ R₁')
    (adj₂' : L₂' ⊣ R₂') (adj₃' : L₃' ⊣ R₃') (e : L₃ ≅ L₁ ⋙ L₂) (e' : L₃' ≅ L₁' ⋙ L₂')
    {G : A ⥤ A'} {H : B ⥤ B'} {K : C ⥤ C'}
    (ν₁ : G ⋙ L₁' ⟶ L₁ ⋙ H) (ν₂ : H ⋙ L₂' ⟶ L₂ ⋙ K) (ν₃ : G ⋙ L₃' ⟶ L₃ ⋙ K)
    (h : ∀ a : A, ν₃.app a ≫ K.map (e.hom.app a) =
      e'.hom.app (G.obj a) ≫ L₂'.map (ν₁.app a) ≫ ν₂.app (L₁.obj a))
    (χ₁ : R₁ ⋙ G ⟶ H ⋙ R₁') (hχ₁ : χ₁ = (mateEquiv adj₁ adj₁' ν₁))
    (χ₂ : R₂ ⋙ H ⟶ K ⋙ R₂') (hχ₂ : χ₂ = (mateEquiv adj₂ adj₂' ν₂))
    (χ₃ : R₃ ⋙ G ⟶ K ⋙ R₃') (hχ₃ : χ₃ = (mateEquiv adj₃ adj₃' ν₃)) (c : C) :
    χ₃.app c ≫ (conjugateIsoEquiv adj₃' (adj₁'.comp adj₂') e'.symm).hom.app (K.obj c) =
      G.map ((conjugateIsoEquiv adj₃ (adj₁.comp adj₂) e.symm).hom.app c) ≫
        χ₁.app (R₂.obj c) ≫ R₁'.map (χ₂.app c) := by
  subst hχ₁ hχ₂ hχ₃
  exact mateEquiv_app_comp_conjugateIsoEquiv_hom_app adj₁ adj₂ adj₃ adj₁' adj₂' adj₃' e e' ν₁ ν₂
    ν₃ h c

/-- The conjugate of a composition isomorphism of left adjoints restricted to full subcategories
is the restriction of the conjugate, if the units, counits and the composition isomorphism are
the restrictions of the ambient ones. -/
lemma conjugateIsoEquiv_lift_aux {A B C : Type*} [Category A] [Category B] [Category C]
    {PA : ObjectProperty A} {PB : ObjectProperty B} {PC : ObjectProperty C}
    {Lg : C ⥤ B} {Rg : B ⥤ C} {Lf : B ⥤ A} {Rf : A ⥤ B} {Lfg : C ⥤ A} {Rfg : A ⥤ C}
    (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adjfg : Lfg ⊣ Rfg)
    {hLg : ∀ K, PB ((PC.ι ⋙ Lg).obj K)} {hRg : ∀ K, PC ((PB.ι ⋙ Rg).obj K)}
    {hLf : ∀ K, PA ((PB.ι ⋙ Lf).obj K)} {hRf : ∀ K, PB ((PA.ι ⋙ Rf).obj K)}
    {hLfg : ∀ K, PA ((PC.ι ⋙ Lfg).obj K)} {hRfg : ∀ K, PC ((PA.ι ⋙ Rfg).obj K)}
    (adjg₀ : PB.lift (PC.ι ⋙ Lg) hLg ⊣ PC.lift (PB.ι ⋙ Rg) hRg)
    (adjf₀ : PA.lift (PB.ι ⋙ Lf) hLf ⊣ PB.lift (PA.ι ⋙ Rf) hRf)
    (adjfg₀ : PA.lift (PC.ι ⋙ Lfg) hLfg ⊣ PC.lift (PA.ι ⋙ Rfg) hRfg)
    (hug : ∀ K, (adjg₀.unit.app K).hom = adjg.unit.app K.obj)
    (huf : ∀ K, (adjf₀.unit.app K).hom = adjf.unit.app K.obj)
    (hcfg : ∀ K, (adjfg₀.counit.app K).hom = adjfg.counit.app K.obj)
    (e : Lfg ≅ Lg ⋙ Lf)
    (e₀ : PA.lift (PC.ι ⋙ Lfg) hLfg ≅ PB.lift (PC.ι ⋙ Lg) hLg ⋙ PA.lift (PB.ι ⋙ Lf) hLf)
    (he : ∀ K, (e₀.hom.app K).hom = e.hom.app K.obj) (K : PA.FullSubcategory) :
    ((conjugateIsoEquiv adjfg₀ (adjg₀.comp adjf₀) e₀.symm).hom.app K).hom =
      (conjugateIsoEquiv adjfg (adjg.comp adjf) e.symm).hom.app K.obj := by
  have he' : ∀ K, (e₀.inv.app K).hom = e.inv.app K.obj := fun K ↦ by
    rw [← cancel_mono (e.hom.app K.obj), Iso.inv_hom_id_app, ← he,
      ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  simp [conjugateEquiv_apply_app, Adjunction.comp_unit_app, hug, huf, hcfg, he']

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Paste

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Scheme.{u}} {a : A₀ ⟶ B₀} {p' : A₀ ⟶ A₁} {p : B₀ ⟶ B₁}
  {b : A₁ ⟶ B₁} {q' : A₁ ⟶ A₂} {q : B₁ ⟶ B₂} {c : A₂ ⟶ B₂}

/-- **Pasting of pullback comparisons**: the pullback comparison of the square obtained by pasting
the squares `sq₁` and `sq₂` along `b` is the composite of their pullback comparisons, through the
composition isomorphisms `L(p' ≫ q')^* ≅ Lq'^* ⋙ Lp'^*` and `L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*`. -/
lemma pullbackSquareComparison_hom_app_paste (sq₁ : CommSq a p' p b) (sq₂ : CommSq b q' q c)
    (sq : CommSq a (p' ≫ q') (p ≫ q) c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology B₂) Ab.{u + 1}) (condensedRingObj Λ B₂))) :
    (leftDerivedUpperStarComp Λ p' q').hom.app (L((c)^*⟦Λ⟧).obj K) ≫
        L((p')^*⟦Λ⟧).map ((pullbackSquareComparison Λ sq₂).hom.app K) ≫
        (pullbackSquareComparison Λ sq₁).hom.app (L((q)^*⟦Λ⟧).obj K) =
      (pullbackSquareComparison Λ sq).hom.app K ≫
        L((a)^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ p q).hom.app K) :=
  paste_aux _ _ ((leftDerivedUpperStarComp Λ (p' ≫ q') c).inv_hom_id_app K) _ _ _ _ _ _ _ _ _ _
    _ _ _ _ (leftDerivedUpperStarComp_assoc_app Λ p' q' c K)
    (map_pullbackSquareComparison_hom_app Λ sq₂ p' K)
    (pullbackSquareComparison_hom_app_obj Λ sq₁ q K) (pullbackSquareComparison_hom_app Λ sq K)

/-- The composition isomorphism `L(pq)^* ≅ Lq^* ⋙ Lp^*` for a factorization `p ≫ q = pq`: the
transport of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the equality. Stating the
pasting law with it avoids unifying `p ≫ q` with definitionally equal composites of schemes. -/
noncomputable def leftDerivedUpperStarCompOfEq {pq : B₀ ⟶ B₂} (h : p ≫ q = pq) :
    L((pq)^*⟦Λ⟧) ≅ L((q)^*⟦Λ⟧) ⋙ L((p)^*⟦Λ⟧) :=
  Eq.rec (motive := fun pq _ ↦ L((pq)^*⟦Λ⟧) ≅ L((q)^*⟦Λ⟧) ⋙ L((p)^*⟦Λ⟧))
    (leftDerivedUpperStarComp Λ p q) h

/-- `pullbackSquareComparison_hom_app_paste` for arbitrary factorizations `p' ≫ q' = p'q'` and
`p ≫ q = pq` of the edges of the pasted square. -/
lemma pullbackSquareComparison_hom_app_paste_of_eq (sq₁ : CommSq a p' p b)
    (sq₂ : CommSq b q' q c) {p'q' : A₀ ⟶ A₂} {pq : B₀ ⟶ B₂} (h' : p' ≫ q' = p'q')
    (h : p ≫ q = pq) (sq : CommSq a p'q' pq c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology B₂) Ab.{u + 1}) (condensedRingObj Λ B₂))) :
    (leftDerivedUpperStarCompOfEq Λ h').hom.app (L((c)^*⟦Λ⟧).obj K) ≫
        L((p')^*⟦Λ⟧).map ((pullbackSquareComparison Λ sq₂).hom.app K) ≫
        (pullbackSquareComparison Λ sq₁).hom.app (L((q)^*⟦Λ⟧).obj K) =
      (pullbackSquareComparison Λ sq).hom.app K ≫
        L((a)^*⟦Λ⟧).map ((leftDerivedUpperStarCompOfEq Λ h).hom.app K) := by
  subst h' h
  exact pullbackSquareComparison_hom_app_paste Λ sq₁ sq₂ sq K

end Paste

namespace NearbyCyclesModel

variable {X X' Y Y' Z Z' : Scheme.{u}}

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}

/-- The composite of morphisms of models `φ : M ⟶ N` over `f, f'` and `ψ : N ⟶ P` over `g, g'`,
over `f ≫ g, f' ≫ g'`. -/
@[simps]
def Hom.comp (φ : M.Hom N f f') (ψ : N.Hom P g g') : M.Hom P (f ≫ g) (f' ≫ g') where
  total := φ.total ≫ ψ.total
  generic := φ.generic ≫ ψ.generic
  comm_j := by rw [Category.assoc, ψ.comm_j, reassoc_of% φ.comm_j]
  comm_i := by rw [Category.assoc, ψ.comm_i, reassoc_of% φ.comm_i]
  comm_ε := by rw [Category.assoc, ψ.comm_ε, reassoc_of% φ.comm_ε]

namespace Hom

variable (φ : M.Hom N f f') (ψ : N.Hom P g g')

/-- **Composition law of the pullback exchanges**, for a morphism of models `χ` over arbitrary
factorizations `f ≫ g = fg` and `f' ≫ g' = fg'` whose morphisms of total spaces and of geometric
generic fibres are the composites: `α_χ ∘ c_{f,g} = α_φ(Lg^*) ∘ Lf'^* α_ψ ∘ c_{f',g'}`. -/
lemma pullbackExchange_comp_app_of_eq {fg : X ⟶ Z} {fg' : X' ⟶ Z'} (χ : M.Hom P fg fg')
    (h : f ≫ g = fg) (h' : f' ≫ g' = fg') (htot : φ.total ≫ ψ.total = χ.total)
    (hgen : φ.generic ≫ ψ.generic = χ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (χ.pullbackExchange Λ).app C ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarCompOfEq Λ h).hom.app C) =
      (leftDerivedUpperStarCompOfEq Λ h').hom.app ((P.nearbyCycles Λ).obj C) ≫
        L((f')^*⟦Λ⟧).map ((ψ.pullbackExchange Λ).app C) ≫
        (φ.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C) :=
  (pullbackExchange_comp_aux (derivedUpperStarLowerStarAdjunction Λ P.j)
    (derivedUpperStarLowerStarAdjunction Λ N.j) (derivedUpperStarLowerStarAdjunction Λ M.j)
    (leftDerivedUpperStarCompOfEq Λ h).hom (leftDerivedUpperStarCompOfEq Λ h').hom
    (leftDerivedUpperStarCompOfEq Λ htot).hom (leftDerivedUpperStarCompOfEq Λ hgen).hom
    (pullbackSquareComparison Λ ψ.commSq_i).hom (pullbackSquareComparison Λ φ.commSq_i).hom
    (pullbackSquareComparison Λ χ.commSq_i).hom
    (pullbackSquareComparison Λ ψ.commSq_j) (pullbackSquareComparison Λ φ.commSq_j)
    (pullbackSquareComparison Λ χ.commSq_j)
    (pullbackSquareComparison Λ ψ.commSq_ε).hom (pullbackSquareComparison Λ φ.commSq_ε).hom
    (pullbackSquareComparison Λ χ.commSq_ε).hom
    (fun K ↦ pullbackSquareComparison_hom_app_paste_of_eq Λ φ.commSq_i ψ.commSq_i h' htot
      χ.commSq_i K)
    (pullbackSquareComparison Λ ψ.commSq_j.flip).hom
    (congrArg Iso.hom (pullbackSquareComparison_flip Λ ψ.commSq_j))
    (pullbackSquareComparison Λ φ.commSq_j.flip).hom
    (congrArg Iso.hom (pullbackSquareComparison_flip Λ φ.commSq_j))
    (pullbackSquareComparison Λ χ.commSq_j.flip).hom
    (congrArg Iso.hom (pullbackSquareComparison_flip Λ χ.commSq_j))
    (fun K ↦ pullbackSquareComparison_hom_app_paste_of_eq Λ φ.commSq_j.flip ψ.commSq_j.flip
      hgen htot χ.commSq_j.flip K)
    (fun C ↦ pullbackSquareComparison_hom_app_paste_of_eq Λ φ.commSq_ε ψ.commSq_ε hgen h
      χ.commSq_ε C)
    (ψ.pullbackExchange Λ) rfl (φ.pullbackExchange Λ) rfl (χ.pullbackExchange Λ) rfl C).symm

/-- **Composition law of the pullback exchanges** (blueprint `prose-E-03`):
`α_{φψ} ∘ c_{f,g} = α_φ(Lg^*) ∘ Lf'^* α_ψ ∘ c_{f',g'}`, where `c` are the composition
isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of derived pullbacks. -/
lemma pullbackExchange_comp_app
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    ((φ.comp ψ).pullbackExchange Λ).app C ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarComp Λ f g).hom.app C) =
      (leftDerivedUpperStarComp Λ f' g').hom.app ((P.nearbyCycles Λ).obj C) ≫
        L((f')^*⟦Λ⟧).map ((ψ.pullbackExchange Λ).app C) ≫
        (φ.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C) :=
  φ.pullbackExchange_comp_app_of_eq Λ ψ (φ.comp ψ) rfl rfl (comp_total φ ψ).symm
    (comp_generic φ ψ).symm C

/-- **Composition law of the pushforward exchanges**, for a morphism of models `χ` over arbitrary
factorizations `f ≫ g = fg` and `f' ≫ g' = fg'` whose morphisms of total spaces and of geometric
generic fibres are the composites. -/
lemma pushforwardExchange_comp_app_of_eq {fg : X ⟶ Z} {fg' : X' ⟶ Z'} (χ : M.Hom P fg fg')
    (h : f ≫ g = fg) (h' : f' ≫ g' = fg') (htot : φ.total ≫ ψ.total = χ.total)
    (hgen : φ.generic ≫ ψ.generic = χ.generic)
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (χ.pushforwardExchange Λ).app E ≫
        (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ fg')
          ((derivedUpperStarLowerStarAdjunction Λ g').comp
            (derivedUpperStarLowerStarAdjunction Λ f'))
          (leftDerivedUpperStarCompOfEq Λ h').symm).hom.app ((M.nearbyCycles Λ).obj E) =
      (P.nearbyCycles Λ).map
          ((conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ fg)
            ((derivedUpperStarLowerStarAdjunction Λ g).comp
              (derivedUpperStarLowerStarAdjunction Λ f))
            (leftDerivedUpperStarCompOfEq Λ h).symm).hom.app E) ≫
        (ψ.pushforwardExchange Λ).app (R((f)_*⟦Λ⟧).obj E) ≫
        R((g')_*⟦Λ⟧).map ((φ.pushforwardExchange Λ).app E) :=
  mateEquiv_comp_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ fg)
    (derivedUpperStarLowerStarAdjunction Λ g') (derivedUpperStarLowerStarAdjunction Λ f')
    (derivedUpperStarLowerStarAdjunction Λ fg') (leftDerivedUpperStarCompOfEq Λ h)
    (leftDerivedUpperStarCompOfEq Λ h') (ψ.pullbackExchange Λ) (φ.pullbackExchange Λ)
    (χ.pullbackExchange Λ) (φ.pullbackExchange_comp_app_of_eq Λ ψ χ h h' htot hgen)
    (ψ.pushforwardExchange Λ) rfl (φ.pushforwardExchange Λ) rfl (χ.pushforwardExchange Λ) rfl E

/-- **Composition law of the pushforward exchanges** (blueprint `prose-E-03`):
`χ_{φψ} = Rg'_*(χ_φ) ∘ χ_ψ(Rf_*)`, through the composition isomorphisms
`R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` and `R(f' ≫ g')_* ≅ Rf'_* ⋙ Rg'_*`, the conjugates of the composition
isomorphisms of derived pullbacks. -/
lemma pushforwardExchange_comp_app
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((φ.comp ψ).pushforwardExchange Λ).app E ≫
        (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ (f' ≫ g'))
          ((derivedUpperStarLowerStarAdjunction Λ g').comp
            (derivedUpperStarLowerStarAdjunction Λ f'))
          (leftDerivedUpperStarComp Λ f' g').symm).hom.app ((M.nearbyCycles Λ).obj E) =
      (P.nearbyCycles Λ).map
          ((conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
            ((derivedUpperStarLowerStarAdjunction Λ g).comp
              (derivedUpperStarLowerStarAdjunction Λ f))
            (leftDerivedUpperStarComp Λ f g).symm).hom.app E) ≫
        (ψ.pushforwardExchange Λ).app (R((f)_*⟦Λ⟧).obj E) ≫
        R((g')_*⟦Λ⟧).map ((φ.pushforwardExchange Λ).app E) :=
  mateEquiv_comp_aux (derivedUpperStarLowerStarAdjunction Λ g)
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (derivedUpperStarLowerStarAdjunction Λ g') (derivedUpperStarLowerStarAdjunction Λ f')
    (derivedUpperStarLowerStarAdjunction Λ (f' ≫ g')) (leftDerivedUpperStarComp Λ f g)
    (leftDerivedUpperStarComp Λ f' g') (ψ.pullbackExchange Λ) (φ.pullbackExchange Λ)
    ((φ.comp ψ).pullbackExchange Λ) (φ.pullbackExchange_comp_app Λ ψ)
    (ψ.pushforwardExchange Λ) rfl (φ.pushforwardExchange Λ) rfl
    ((φ.comp ψ).pushforwardExchange Λ) rfl E

end Hom

end NearbyCyclesModel

/-! ### Bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

set_option hygiene false in
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

/-- On the ambient derived category, the composition isomorphism `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` on
bounded constructible complexes is the conjugate of the composition isomorphism
`ProEtale.CondensedRing.leftDerivedUpperStarComp` (transported along
`f.left ≫ g.left = (f ≫ g).left`). -/
lemma boundedConstructibleLowerStarComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerStarComp ℓ f g).inv.app K).hom =
      (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λℓ (f ≫ g).left)
        ((derivedUpperStarLowerStarAdjunction Λℓ g.left).comp
          (derivedUpperStarLowerStarAdjunction Λℓ f.left))
        (leftDerivedUpperStarCompOfEq Λℓ (Over.comp_left _ _ _ f g).symm).symm).hom.app K.obj :=
  conjugateIsoEquiv_lift_aux (derivedUpperStarLowerStarAdjunction Λℓ g.left)
    (derivedUpperStarLowerStarAdjunction Λℓ f.left)
    (derivedUpperStarLowerStarAdjunction Λℓ (f ≫ g).left)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f ≫ g))
    (boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom ℓ (f ≫ g))
    (leftDerivedUpperStarCompOfEq Λℓ (Over.comp_left _ _ _ f g).symm)
    (boundedConstructibleUpperStarComp Λℓ ℓ f g)
    (fun K ↦ boundedConstructibleUpperStarComp_hom_app_hom Λℓ ℓ f g K) K

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
