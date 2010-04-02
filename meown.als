//NOTA: Qualquer referência no seguinte texto a elevadores e andares é pura
//coincidência e não deve ser levada a sério.
open util/ordering[State]
 
abstract sig Local {}

sig State {
	//carruagens e pessoas sao as unicas coisas que mudam de sitio
	localActualDeCarruagem: Carruagem set -> one Paragem,
	localActualDePessoa: Pessoa set -> one Local,
	
	//direccoes que mudam (ter uma direccao em pessoa nao torna desnecessario ter direccao em paragem?)
	direccaoCarruagem: Carruagem set -> one Direccao,
	direccaoParagem: Paragem set -> one Direccao,
	direccaoPessoa: Pessoa set -> one Direccao,

	//proximos destinos da carruagem mudam (ver se tem interesse ter uma lista aqui)
	destinosCarruagem: Carruagem set -> set Paragem
}
 
sig Paragem extends Local {
	seguinte: lone Paragem
}
 
sig Carruagem extends Local{
}
 
sig Pessoa {
	destino: one Paragem
}
 
abstract sig Direccao {}
 
one sig Direita, Esquerda, Nenhuma, Ambas extends Direccao {}
 
//------------------------------------------------------------------------------------------------
//----------------------------------- Restringir "seguinte" ---------------------------------
//------------------------------------------------------------------------------------------------
fact aUltimaParagemLigaSempreAPrimeira
{
	all p1: Paragem, p2: Paragem | p2 in p1.^seguinte
}
 
fact naoHaParagemSeguinteIgualParaDuasParagensDiferentes {
	all p1: Paragem, p2: Paragem, p3:Paragem | 
	(p1 != p3 && (p1.seguinte = p2)) => !(p3.seguinte = p2)
}

fact ambasApenasPodeExistirEmParagem {
	!(Ambas in (State.direccaoCarruagem[Carruagem]  + State.direccaoPessoa[Pessoa]))
}

//------------------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------------------

pred estadoInicial[s: State] {
	all c1: Carruagem, c2: Carruagem | s.localActualDeCarruagem[c1] = s.localActualDeCarruagem[c2]
	s.direccaoPessoa[Pessoa] = Nenhuma
//	all c: Carruagem | s.direccaoCarruagem[c] = Nenhuma
	s.direccaoParagem[Paragem] = Nenhuma
}

pred estadosSeguintes[s: State] {
	
}

fact inicio {
	estadoInicial[first]
}


//------------------------------------------------------------------------------------------------
//--------------------------------------------- Pred's ------------------------------------------
//------------------------------------------------------------------------------------------------
pred movimentacaoDeUmaCarruagem[s, s': State, c1: Carruagem] {
	let p1 = s.localActualDeCarruagem[c1] 
	{
		(s.direccaoCarruagem[c1] = Nenhuma) implies
				(s'.localActualDeCarruagem = s.localActualDeCarruagem) 
		else 
		(s.direccaoCarruagem[c1] = Direita) implies
				(s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> p1.seguinte))
		else
		(s.direccaoCarruagem[c1] = Esquerda) implies 
				(s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> seguinte.p1))
		s'.destinosCarruagem = s.destinosCarruagem - (c1 -> p1)
	}
	s'.localActualDePessoa = s.localActualDePessoa
	s'.direccaoCarruagem = s.direccaoCarruagem
	s'.direccaoParagem = s.direccaoParagem
	s'.direccaoPessoa = s.direccaoPessoa
}

//------------------------------------------------------------------------------------------------
//--------------------------------------- Cheques (em branco ou não) -------------------
//------------------------------------------------------------------------------------------------
 
fact motor {
	all s : State, s' : s.next | some c: Carruagem | movimentacaoDeUmaCarruagem[s,s',c]
}
 
assert cond1 {
	one s: first | all p: Pessoa | s.direccaoPessoa[p] = Nenhuma
}
//check cond1
assert cond2 {
	one s: first | all c: Carruagem | s.direccaoCarruagem[c] = Nenhuma
}
//check cond2
assert cond3 {
	one s: first | all p: Paragem | s.direccaoParagem[p] = Nenhuma
}
//check cond3
assert cond4 {
	all s: State | all c: Carruagem | s.direccaoCarruagem[c] = Nenhuma
}
check cond4 for 8 but exactly 3 Paragem, exactly 2 Pessoa
//run {} for 4
