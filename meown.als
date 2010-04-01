//NOTA: Qualquer referência no seguinte texto a elevadores e andares é pura
//coincidência e não deve ser levada a sério.
open util/ordering[State]
 
sig State {
	//carruagens e pessoas sao as unicas coisas que mudam de sitio
	localActualDeCarruagem: Carruagem set -> one Paragem,
	carruagemActualDePessoa: Pessoa set -> one Carruagem,
	paragemActualDePessoaAEspera: Pessoa set -> one Paragem,
	
	//direccoes que mudam (ter uma direccao em pessoa nao torna desnecessario ter direccao em paragem?)
	direccaoCarruagem: Carruagem set -> one Direccao,
	direccaoParagem: Paragem set -> one Direccao,
	direccaoPessoa: Pessoa set -> one Direccao,

	//proximos destinos da carruagem mudam (ver se tem interesse ter uma lista aqui)
	destinosCarruagem: Carruagem set -> set Paragem
}
 
sig Paragem {
	seguinte: lone Paragem
}
 
sig Carruagem {
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
	all p1: Paragem | p1 in p1.^seguinte
}
 
fact naoHaParagemSeguinteIgualParaDuasParagensDiferentes {
	all p1: Paragem, p2: Paragem, p3:Paragem | 
	(p1 != p3 && (p1.seguinte = p2)) => !(p3.seguinte = p2)
}

fact ambasApenasPodeExistirEmParagem {
	all s: State, p: Pessoa, c: Carruagem | Ambas not in (s.direccaoCarruagem[c]  + s.direccaoPessoa[p])
}
//------------------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------------------

pred estadoInicial[s: State] {
	all c1: Carruagem, c2: Carruagem | s.localActualDeCarruagem[c1] = s.localActualDeCarruagem[c2]
	all p: Pessoa | s.direccaoPessoa[p] = Nenhuma
	all c: Carruagem | s.direccaoCarruagem[c] = Nenhuma
	all pa: Paragem | s.direccaoParagem[pa] = Nenhuma
	
}

fact inicio {
	estadoInicial[first]
}

/*
//------------------------------------------------------------------------------------------------
//--------------------------------------------- Pred's ------------------------------------------
//------------------------------------------------------------------------------------------------
pred movimentacaoCarruagem[s, s': State, c1: Carruagem] {
	let p1 = s.localActual[c1] 
	{
		(movimento[c1] = Nenhuma) implies
				(s'.localActual = s.localActual) 
		else 
		(movimento[c1] = Direita) implies
				(s'.localActual = s.localActual ++ (c1 -> p1.seguinte))
		else
		(movimento[c1] = Esquerda) implies 
				(s'.localActual = s.localActual ++ (c1 -> seguinte.p1))
	}
}
 
//------------------------------------------------------------------------------------------------
//--------------------------------------- Cheques (em branco ou não) -------------------
//------------------------------------------------------------------------------------------------
 
fact motor {
	all c1: Carruagem | c1.movimento = Nenhuma
	all s : State, s' : s.next | some c: Carruagem | some d: Direccao | movimentacaoCarruagem[s,s',c]
}
 */
//check verificar for 6
//check verMovimentoSenaoTamosLixadosNaoSeVeNada for 6
run {} for 4
