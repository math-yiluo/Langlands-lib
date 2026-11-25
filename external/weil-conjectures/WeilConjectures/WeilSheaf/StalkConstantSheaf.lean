/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# Transports of the unit section of the constant sheaf

The transport of global sections along a commutative square and the canonical morphism
`g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` maps the restriction of the unit section of `ℚ̄_ℓ` to the restriction of the unit
section
(`AlgebraicGeometry.ProEtale.globalSectionsTransport_globalSectionsToUpperStar_oneGlobalSection`).
The iterated Weil structures of the constant Weil sheaf are the canonical morphisms
(`AlgebraicGeometry.WeilSheaf.frobeniusPowStr_adicConstant`), so the Frobenius of the stalks of
`ℚ̄_ℓ` fixes the unit section.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- Restrictions of global sections along equal morphisms agree. -/
lemma globalSectionsToUpperStar_app_comp_upperStarCongr {A : Type*} [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {Z W : Scheme.{u}} {a b : Z ⟶ W} (p : a = b)
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (globalSectionsToUpperStar A a).app F ≫ (Sheaf.Γ _ A).map ((upperStarCongr A p).hom.app F) =
      (globalSectionsToUpperStar A b).app F := by
  subst p
  simp [upperStarCongr]

/-- The restriction of global sections of a sheaf `F` along `t` followed by the transport along a
commutative square `τ ≫ t = t' ≫ g` and a morphism `ψ : g^* F ⟶ F'` is the restriction along `g`,
followed by the restriction along `t'` and by `ψ`. -/
lemma globalSectionsToUpperStar_app_comp_globalSectionsTransport {A : Type*}
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {P P' Y Y' : Scheme.{u}} {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) {F : Sheaf (Scheme.ProEt.topology Y) A}
    {F' : Sheaf (Scheme.ProEt.topology Y') A} (ψ : (g)^*[A].obj F ⟶ F') :
    (globalSectionsToUpperStar A t).app F ≫ globalSectionsTransport A h ψ =
      (globalSectionsToUpperStar A g).app F ≫ (globalSectionsToUpperStar A t').app _ ≫
        (Sheaf.Γ _ A).map ((t')^*[A].map ψ) := by
  rw [← reassoc_of% globalSectionsToUpperStar_comp, globalSectionsTransport,
    ← reassoc_of% globalSectionsToUpperStar_comp,
    ← globalSectionsToUpperStar_app_comp_upperStarCongr h, Category.assoc]
  simp only [← Functor.map_comp]
  rw [upperStarCompIso_hom_app, Category.assoc, Iso.hom_inv_id_app_assoc, Category.assoc]

/-- **Transport of the unit section.** The transport of global sections along a commutative
square `τ ≫ t = t' ≫ g` and the canonical morphism `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` maps the restriction along
`t` of the unit section of `ℚ̄_ℓ` to its restriction along `t'`. -/
lemma globalSectionsTransport_globalSectionsToUpperStar_oneGlobalSection
    {P P' Y Y' : Scheme.{u}} {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) :
    (globalSectionsTransport _ h (upperStarAdicConstantSheafHom l g)).hom
        (((globalSectionsToUpperStar _ t).app (adicConstantSheaf l Y)).hom (oneGlobalSection Y)) =
      ((globalSectionsToUpperStar _ t').app (adicConstantSheaf l Y')).hom
        (oneGlobalSection Y') := by
  have e := congrArg (fun φ ↦ φ.hom (oneGlobalSection (l := l) Y))
    (globalSectionsToUpperStar_app_comp_globalSectionsTransport h
      (upperStarAdicConstantSheafHom l g))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  have n := congrArg (fun φ ↦ φ.hom (((globalSectionsToUpperStar _ g).app
    (adicConstantSheaf l Y)).hom (oneGlobalSection Y)))
    ((globalSectionsToUpperStar (WeilCoefficients.{u} l) t').naturality
      (upperStarAdicConstantSheafHom l g))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n
  refine e.trans (n.symm.trans ?_)
  exact congrArg _ (Γ_map_adicUpperStarUnitIso_globalSectionsToUpperStar_oneGlobalSection g)

/-- The comparison `ℚ̄_ℓ,V ⟶ g_* ℚ̄_ℓ,W` pulls functions back along `V' ×_V W ⟶ V'`. -/
lemma adicConstantSheafToLowerStar_hom_app {V W : Scheme.{u}} (g : W ⟶ V) (U : V.ProEtᵒᵖ) :
    (adicConstantSheafToLowerStar l g).hom.app U =
      (adicFunctionsPresheaf l).map (pullback.fst U.unop.hom g).op :=
  rfl

/-- The inverse of `e_* ℚ̄_ℓ ≅ ℚ̄_ℓ` is the pullback of functions along `e`. -/
lemma adicConstantSheafLowerStarIso_inv {X Y : Scheme.{u}} (e : X ≅ Y) :
    (adicConstantSheafLowerStarIso l e).inv = adicConstantSheafToLowerStar l e.hom := by
  ext V : 3
  rw [adicConstantSheafLowerStarIso_inv_hom_app, adicConstantSheafToLowerStar_hom_app]

/-- Adjoint transposes of morphisms out of pullbacks along equal morphisms. -/
lemma homEquiv_upperStarCongr_hom_app_comp {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Z W : Scheme.{u}} {a b : Z ⟶ W} (p : a = b)
    {M : Sheaf (Scheme.ProEt.topology W) A} {N : Sheaf (Scheme.ProEt.topology Z) A}
    (f : (b)^*[A].obj M ⟶ N) :
    ((upperStarLowerStarAdjunction A a).homEquiv _ _) ((upperStarCongr A p).hom.app M ≫ f) =
      ((upperStarLowerStarAdjunction A b).homEquiv _ _) f ≫
        (lowerStarCongr A p.symm).hom.app N := by
  subst p
  simp [upperStarCongr, lowerStarCongr]

/-- Naturality of the composition isomorphisms of pullbacks. -/
@[reassoc]
lemma upperStarComp_hom_app_comp_map_map {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {P Z Y : Scheme.{u}} (a : P ⟶ Z) (b : Z ⟶ Y)
    {M M' : Sheaf (Scheme.ProEt.topology Y) A} (f : M ⟶ M') :
    (upperStarComp A a b).hom.app M ≫ (a)^*[A].map ((b)^*[A].map f) =
      (a ≫ b)^*[A].map f ≫ (upperStarComp A a b).hom.app M' :=
  ((upperStarComp A a b).hom.naturality f).symm

/-- Naturality of the congruence isomorphisms of pullbacks. -/
@[reassoc]
lemma upperStarCongr_hom_app_comp_map {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Z Y : Scheme.{u}} {a b : Z ⟶ Y} (p : a = b)
    {M M' : Sheaf (Scheme.ProEt.topology Y) A} (f : M ⟶ M') :
    (upperStarCongr A p).hom.app M ≫ (b)^*[A].map f =
      (a)^*[A].map f ≫ (upperStarCongr A p).hom.app M' :=
  ((upperStarCongr A p).hom.naturality f).symm

/-- The components of the factorisation isomorphism `a^* ≅ c^* ⋙ b^*` of pullbacks. -/
lemma upperStarFactor_hom_app {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {P Z Y : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Z} {c : Z ⟶ Y}
    (e : b ≫ c = a) (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarFactor A e).hom.app M =
      (upperStarCongr A e.symm).hom.app M ≫ (upperStarComp A b c).hom.app M :=
  rfl

/-- The adjoint transpose, along `a^* ⊣ a_*`, of the morphism `a^* M ≅ b^* c^* M ⟶ b^* b_* N ⟶ N`
induced by `β : c^* M ⟶ b_* N` and a factorisation `b ≫ c = a` is `M ⟶ c_* c^* M ⟶ c_* b_* N ≅
a_* N`. -/
lemma homEquiv_upperStarFactor_hom_app_comp_counit {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {P Z Y : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Z} {c : Z ⟶ Y}
    (e : b ≫ c = a) (M : Sheaf (Scheme.ProEt.topology Y) A) (N : Sheaf (Scheme.ProEt.topology P) A)
    (β : (c)^*[A].obj M ⟶ (b)_*[A].obj N) :
    ((upperStarLowerStarAdjunction A a).homEquiv _ _)
        ((upperStarFactor A e).hom.app M ≫ (b)^*[A].map β ≫
          (upperStarLowerStarAdjunction A b).counit.app N) =
      (upperStarLowerStarAdjunction A c).unit.app M ≫ (c)_*[A].map β ≫
        (lowerStarFactor A e).hom.app N := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor]
  congr 1
  have n := (lowerStarFactor A e).hom.naturality
    ((b)^*[A].map β ≫ (upperStarLowerStarAdjunction A b).counit.app N)
  simp only [Functor.comp_map] at n
  rw [← n, ← Functor.map_comp_assoc]
  congr 2
  have h := ((upperStarLowerStarAdjunction A b).homEquiv _ _).apply_symm_apply β
  rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilCoefficients

variable {l : ℕ} [Fact l.Prime]

/-- An endomorphism of a line fixing a nonzero vector is the identity. -/
lemma eq_id_of_finrank_eq_one {M : WeilCoefficients.{u} l} (f : M ⟶ M)
    (hM : Module.finrank (PadicAlgCl l) ((toModuleCat l).obj M) = 1)
    (v : (toModuleCat l).obj M) (hv : v ≠ 0) (hf : ((toModuleCat l).map f).hom v = v) :
    f = 𝟙 M := by
  ext x
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).1 hM x
  exact (((toModuleCat l).map f).hom.map_smul c v).trans (congrArg (c • ·) hf)

end AlgebraicGeometry.WeilCoefficients

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The Weil structure of the constant Weil sheaf `ℚ̄_ℓ` is the canonical morphism
`Fr^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`. -/
lemma frobeniusStr_adicConstant :
    (adicConstant k₀ l X).frobeniusStr = ProEtale.upperStarAdicConstantSheafHom l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom :=
  ProEtale.upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso


omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The canonical morphisms `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along equal morphisms agree. -/
lemma _root_.AlgebraicGeometry.ProEtale.upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom
    {Z W : Scheme.{u}} {a b : Z ⟶ W} (p : a = b) :
    (ProEtale.upperStarCongr _ p).hom.app (ProEtale.adicConstantSheaf l W) ≫
        ProEtale.upperStarAdicConstantSheafHom l b =
      ProEtale.upperStarAdicConstantSheafHom l a := by
  subst p
  simp [ProEtale.upperStarCongr]

variable (k₀ l X) in
/-- The iterated Weil structures `φ_m`, `m ≥ 1`, of the constant Weil sheaf `ℚ̄_ℓ` are the
canonical morphisms `(Frᵐ)^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, by the cocycle condition
`AlgebraicGeometry.ProEtale.upperStarAdicConstantSheafHom_comp`. -/
lemma frobeniusPowStr_adicConstant (m : ℕ) (hm : 1 ≤ m) :
    (adicConstant k₀ l X).frobeniusPowStr m = ProEtale.upperStarAdicConstantSheafHom l
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [frobeniusPowStr_one _ (congrArg (fun e ↦ e.asIso.hom)
      (pow_one (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius)),
      frobeniusStr_adicConstant]
    exact ProEtale.upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom _
  | succ m hm ih =>
    have e : (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).asIso.hom := by
      rw [pow_succ, Aut.mul_asIso, Iso.trans_hom]
    rw [← upperStarFactor_hom_app_comp_frobeniusPowStr_succ _ m e, ih, frobeniusStr_adicConstant,
      ProEtale.upperStarFactor, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    exact (congrArg (_ ≫ ·) (ProEtale.upperStarAdicConstantSheafHom_comp l _ _)).trans
      (ProEtale.upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom _)


/-- The Weil structures `Fr^* F ⟶ F` on underlying sheaves are natural in `F`. -/
lemma frobeniusStr_naturality {F G : WeilSheaf k₀ l X} (f : F ⟶ G) :
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[
      WeilCoefficients.{u} l].map
        f.hom.hom.f.hom ≫ G.frobeniusStr = F.frobeniusStr ≫ f.hom.hom.f.hom := by
  have n := (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).hom.naturality f.hom.hom.f.hom
  rw [frobeniusStr, frobeniusStr, ← Category.assoc, n, Category.assoc, Category.assoc]
  congr 1
  have h := congrArg (fun g ↦ g.hom) f.hom.hom.h
  simp only [Mod.comp_hom'] at h
  exact h


end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The stalks of the constant sheaf `ℚ̄_ℓ` at points with values in a field are lines. -/
lemma finrank_globalSections_upperStar_adicConstantSheaf {K : Type u} [Field K] {Y : Scheme.{u}}
    (t : Spec (.of K) ⟶ Y) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj ((t)^*[_].obj (adicConstantSheaf l Y)))) = 1 :=
  (WeilCoefficients.linearEquivOfIso ((Sheaf.Γ _ _).mapIso
    (asIso (upperStarAdicConstantSheafHom l t)))).finrank_eq.trans
    (finrank_globalSections_adicConstantSheaf _)

/-- The restriction of the unit section of `ℚ̄_ℓ` to a point with values in a field is
nonzero. -/
lemma globalSectionsToUpperStar_oneGlobalSection_ne_zero {K : Type u} [Field K]
    {Y : Scheme.{u}} (t : Spec (.of K) ⟶ Y) :
    ((globalSectionsToUpperStar _ t).app (adicConstantSheaf l Y)).hom (oneGlobalSection Y) ≠ 0 := by
  intro h
  have e := Γ_map_adicUpperStarUnitIso_globalSectionsToUpperStar_oneGlobalSection (l := l) t
  rw [h, map_zero] at e
  exact oneGlobalSection_ne_zero _ e.symm

/-- **Transports of stalks of `ℚ̄_ℓ` are trivial.** At a point `t` with values in a field, a
composite of transports along commutative squares `τ ≫ t = t' ≫ g` and `τ' ≫ t' = t ≫ g'` and the
canonical morphisms `g^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, `g'^* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is the identity: both fix the restriction
of the unit section, which spans the line `Γ(Spec K, t^* ℚ̄_ℓ)`. -/
lemma globalSectionsTransport_comp_globalSectionsTransport_eq_id {K : Type u} [Field K]
    {Y Y' : Scheme.{u}} {τ τ' : Spec (.of K) ⟶ Spec (.of K)} {t : Spec (.of K) ⟶ Y}
    {t' : Spec (.of K) ⟶ Y'} {g : Y' ⟶ Y} {g' : Y ⟶ Y'} (h : τ ≫ t = t' ≫ g)
    (h' : τ' ≫ t' = t ≫ g') :
    globalSectionsTransport _ h (upperStarAdicConstantSheafHom l g) ≫
      globalSectionsTransport _ h' (upperStarAdicConstantSheafHom l g') = 𝟙 _ := by
  refine WeilCoefficients.eq_id_of_finrank_eq_one _
    (finrank_globalSections_upperStar_adicConstantSheaf t) _
    (globalSectionsToUpperStar_oneGlobalSection_ne_zero t) ?_
  exact (congrArg _ (globalSectionsTransport_globalSectionsToUpperStar_oneGlobalSection h)).trans
    (globalSectionsTransport_globalSectionsToUpperStar_oneGlobalSection h')

/-- Transports along squares with equal target points agree up to `eqToHom`. -/
lemma globalSectionsTransport_comp_eqToHom {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {P P' Y Y' : Scheme.{u}} {τ : P' ⟶ P} {t : P ⟶ Y}
    {t₁ t₂ : P' ⟶ Y'} {g : Y' ⟶ Y} (h₁ : τ ≫ t = t₁ ≫ g) (h₂ : τ ≫ t = t₂ ≫ g) (p : t₁ = t₂)
    {F : Sheaf (Scheme.ProEt.topology Y) A} {F' : Sheaf (Scheme.ProEt.topology Y') A}
    (ψ : (g)^*[A].obj F ⟶ F') :
    globalSectionsTransport A h₁ ψ ≫
        eqToHom (congrArg (fun s ↦ (Sheaf.Γ _ A).obj ((s)^*[A].obj F')) p) =
      globalSectionsTransport A h₂ ψ := by
  subst p
  simp

/-- Transports along squares with equal source points agree up to `eqToHom`. -/
lemma eqToHom_comp_globalSectionsTransport {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {P P' Y Y' : Scheme.{u}} {τ : P' ⟶ P} {t₁ t₂ : P ⟶ Y}
    {t' : P' ⟶ Y'} {g : Y' ⟶ Y} (h₁ : τ ≫ t₁ = t' ≫ g) (h₂ : τ ≫ t₂ = t' ≫ g) (p : t₁ = t₂)
    {F : Sheaf (Scheme.ProEt.topology Y) A} {F' : Sheaf (Scheme.ProEt.topology Y') A}
    (ψ : (g)^*[A].obj F ⟶ F') :
    eqToHom (congrArg (fun s ↦ (Sheaf.Γ _ A).obj ((s)^*[A].obj F)) p) ≫
        globalSectionsTransport A h₂ ψ =
      globalSectionsTransport A h₁ ψ := by
  subst p
  simp

end AlgebraicGeometry.ProEtale
