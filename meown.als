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
	direccaoPessoa: Pessoa set -> one Direccao,

	//proximos destinos da carruagem mudam (ver se tem interesse ter uma lista aqui)
	destinosCarruagem: Carruagem set -> set Paragem
}
 
sig Paragem extends Local {
	seguinte: lone Paragem
}

one sig Inicio extends Local { }
one sig Fim extends Local { }
 
sig Carruagem extends Local{
}
 
sig Pessoa {
	destino: one Paragem
}
 
abstract sig Direccao {}
 
one sig Direita, Esquerda, Nenhuma, Ambas extends Direccao {}

//------------------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------------------

pred estadoInicial[s: State] {
	all c1: Carruagem, c2: Carruagem | s.localActualDeCarruagem[c1] = s.localActualDeCarruagem[c2]
	s.direccaoPessoa[Pessoa] = Nenhuma
	s.direccaoCarruagem[Carruagem] = Nenhuma
	s.localActualDePessoa[Pessoa] = Inicio and s.localActualDePessoa[Pessoa] != Fim
	s.destinosCarruagem.Paragem = none
}

pred estadosSeguintes[s: State] {
	all p1: Paragem, p2: Paragem | p2 in p1.^seguinte
	all p1: Paragem, p2: Paragem, p3:Paragem | (p1 != p3 && (p1.seguinte = p2)) => !(p3.seguinte = p2)
	!(Ambas in (State.direccaoCarruagem[Carruagem]  + State.direccaoPessoa[Pessoa]))
}

//------------------------------------------------------------------------------------------------
//--------------------------------------------- Pred's ------------------------------------------
//------------------------------------------------------------------------------------------------

pred movimento[s,s': State] {
		one c1: Carruagem | 	saemPessoas[s,s',c1] || 	//primeiro saem as pessoas da carruagem
											(ninguemMaisPodeSair[s] and entramPessoas[s,s',c1]) || 	//quando não houver mais pessoas na carruagem que queiram sair entram pessoas
											(ninguemMaisPodeSair[s] and ninguemMaisPodeEntrar[s] and movimentaCarruagem[s,s',c1]) 	//quando não houver mais pessoas na carruagem que queiram sair nem mais pessoas na paragem que queiram entrar, a carruagem movimenta-se
}

pred chamada[s,s': State] {
		one p1: Pessoa, par1: Paragem, d1: Direccao | {
//		pré-condicoes		
		p1 in s.localActualDePessoa.Inicio		//a pessoa tem que estar no "local" inicio
		p1.destino != par1								//o destino da pessoa tem que ser diferente do sitio onde chama a carruagem
		d1 != Nenhuma									//a direccao da pessoa não pode ser "nenhuma"
		d1 != Ambas										//nem "ambas"

//		acções
		s'.localActualDePessoa = s.localActualDePessoa ++ (p1 -> par1) 	//coloca a pessoa numa paragem
		s'.direccaoPessoa = s.direccaoPessoa ++ (p1 -> d1)						//a pessoa quer ir numa direccao
		
//		outras condicoes alternativas
		one c1: Carruagem | {
				(s.localActualDeCarruagem.par1 != none) =>							//se existir uma carruagem na paragem onde pessoa foi colocada
				{
						s'.direccaoCarruagem = s.direccaoCarruagem						//não há alteração na direccão da carruagem
						s'.destinosCarruagem = s.destinosCarruagem					//os destinos das carruagens continuam os mesmos (já que ela não pode partir sem que todas as pessoas que pode levar entrem)
				} 
				else (d1 in s.direccaoCarruagem[Carruagem]) =>					//existe alguma carruagem a ir na mesma direccao?
				{
						c1 in s.direccaoCarruagem.d1														//c1 e uma carruagem com a mesma direccao da pessoa
						s'.direccaoCarruagem = s.direccaoCarruagem								//não há alterações na direcção da carruagem (irá chegar à paragem da pessoa)
						s'.destinosCarruagem = s.destinosCarruagem + (c1 -> par1)	//adiciona-se o destino à lista da carruagem, para esta ter que passar por lá
				} 
				else (Nenhuma in s.direccaoCarruagem[Carruagem]) =>				//existe alguma carruagem parada?
				{
						c1 in s.direccaoCarruagem.Nenhuma											//c1 e uma carruagem parada
						s'.direccaoCarruagem = s.direccaoCarruagem	 ++ (c1 -> d1)	//não há alterações na direcção da carruagem (irá chegar à paragem da pessoa)
						s'.destinosCarruagem = s.destinosCarruagem + (c1 -> par1)	//adiciona-se o destino à lista da carruagem, para esta ter que passar por lá
				}
				else 
				{
						s'.direccaoCarruagem = s.direccaoCarruagem								//não há alterações na direcção da carruagem
						s'.destinosCarruagem = s.destinosCarruagem							//adiciona-se o destino à lista da carruagem, para esta ter que passar por lá
				}
				//senão não se faz nada. Espera-se que uma carruagem fique vazia, e mude de direccao
		}

		s'.localActualDeCarruagem = s.localActualDeCarruagem
		}
}

pred ninguemMaisPodeSair[s: State] {
		all c1: Carruagem | no p1: Pessoa |	//para todas as carruagens não existe nenhuma pessoa que
			p1 in s.localActualDePessoa.c1 and 	//encontrando-se dentro de uma carruagem
			s.localActualDeCarruagem[c1] = p1.destino	//essa carruagem esteja parada no seu local de destino
}

pred saemPessoas[s,s': State, c1: Carruagem] {
		one p1: Pessoa | {
		//pré-condicoes
		p1 in s.localActualDePessoa.c1						//pessoa dentro de carruagem
		s.localActualDeCarruagem[c1] = p1.destino	//pessoa dentro da carruagem tem como destino a paragem actual
		
		//accoes
		s'.localActualDePessoa = s.localActualDePessoa ++ (p1 -> Fim)	//coloca a pessoa no fim
		s'.direccaoPessoa = s.direccaoPessoa ++ (p1 -> Nenhuma)			//a pessoa fica com direccao "Nenhuma"
		
		s'.destinosCarruagem = s.destinosCarruagem								//destinos da carruagem ficam iguais
		s'.localActualDeCarruagem = s.localActualDeCarruagem					//local actual da carruagem é o mesmo

		//opcionais
		s'.direccaoCarruagem = s.direccaoCarruagem									//senão continua movimento
		}
}

pred ninguemMaisPodeEntrar[s: State] {
		all c1: Carruagem | no p1: Pessoa | 	//para todas as carruagens não existe nenhuma pessoa que
			s.localActualDePessoa[p1] = s.localActualDeCarruagem[c1] and	//esteja na mesma paragem que uma carruagem e
			s.localActualDeCarruagem[c1] != p1.destino and	//essa carruagem esteja na paragem destino dessa pessoa (logo nenhuma pessoa está no seu destino)
			(s.direccaoPessoa[p1] = s.direccaoCarruagem[c1] or //e a pessoa e a carruagem vao na mesma direccao ou
			s.direccaoCarruagem[c1] = Nenhuma)	//a carruagem esteja parada
}

pred entramPessoas[s,s': State, c1: Carruagem] {
	one p1: Pessoa | {
		//pre-condicoes
		s.localActualDePessoa[p1] = s.localActualDeCarruagem[c1]	//pessoa e carruagem encontram-se na mesma paragem
		s.localActualDeCarruagem[c1] != p1.destino							//pessoa nao se encontra no seu destino
		(s.direccaoPessoa[p1] = s.direccaoCarruagem[c1] or 			//direccao da pessoa e a mesma da carruagem
		s.direccaoCarruagem[c1] = Nenhuma)									//ou entao a carruagem esta parada

		//accoes
		s'.localActualDePessoa = s.localActualDePessoa ++ (p1 -> c1)				//coloca pessoa na carruagem
		s'.destinosCarruagem = s.destinosCarruagem + (c1 -> p1.destino)		//adiciona o destino da pessoa aos destinos da carruagem

		s'.localActualDeCarruagem = s.localActualDeCarruagem		//carruagem mantem-se no mesmo sitio
		s'.direccaoPessoa = s.direccaoPessoa									//direccao da pessoa e o mesmo

		//opcionais
		s.direccaoCarruagem[c1] = Nenhuma => 							//se a carruagem estivesse parada
				s'.direccaoCarruagem = s.direccaoCarruagem ++ (c1 -> s.direccaoPessoa[p1]) 	//passa a mover-se na direccao da pessoa
		else 
				s'.direccaoCarruagem = s.direccaoCarruagem				//senao continua com a mesma direccao
		}
			
}

pred movimentaCarruagem[s,s': State, c1: Carruagem] {
	//pre condicoes
	s.direccaoCarruagem[c1] = Direita or
	s.direccaoCarruagem[c1] = Esquerda

	//accoes
	let p1 = s.localActualDeCarruagem[c1] 				//guarda a paragem actual da carruagem
	{
		(s.direccaoCarruagem[c1] = Direita) implies				//se a carruagem se move para a direita
		{
				s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> p1.seguinte)		 		//continua para a paragem seguinte
				s'.destinosCarruagem = s.destinosCarruagem - (c1 -> p1.seguinte)								//retira a proxima paragem dos destinos da carruagem
		}
		else																				//se a carruagem se move para a esquerda
		{
				s'.localActualDeCarruagem = s.localActualDeCarruagem ++ (c1 -> seguinte.p1)				//continua para a paragem anterior
				s'.destinosCarruagem = s.destinosCarruagem - (c1 -> seguinte.p1)								//retira a proxima paragem dos destinos da carruagem
		}
	}

	s'.localActualDePessoa = s.localActualDePessoa								//as pessoas mantem-se no mesmo sitio
	s'.direccaoPessoa = s.direccaoPessoa												//a direccao das pessoas e a mesma

	//opcionais
	s'.destinosCarruagem[c1] = none =>												//se a carruagem nao tiver mais destinos
		s'.direccaoCarruagem = s.direccaoCarruagem ++ (c1 -> Nenhuma)		//carruagem para
	else
		s'.direccaoCarruagem = s.direccaoCarruagem											//senao continua movimento
}

/* No man left behind */
pred garanteQueTodasAsPessoasSaoLevadas[s,s': State] {
		one c1: Carruagem, p1: Pessoa | {
//				pre condicao
				s.direccaoCarruagem[c1] = Nenhuma			//se uma carruagem estiver parada (direccao Nenhuma)
				p1 in s.localActualDePessoa.Paragem			//e se uma pessoa estiver numa Paragem
				s.localActualDePessoa[p1] not in s.destinosCarruagem[Carruagem]	//e essa mesma paragem nao for o destino de nenhuma carruagem

//				accoes
				s'.direccaoCarruagem = s.direccaoCarruagem ++ (c1 -> Esquerda)		//coloca essa carruagem c1 com direccao esquerda
				s'.destinosCarruagem = s.destinosCarruagem + (c1 -> s.localActualDePessoa[p1])	//e adiciona a paragem dessa pessoa ao destino da carruagem

				s'.localActualDePessoa = s.localActualDePessoa
				s'.localActualDeCarruagem = s.localActualDeCarruagem
				s'.direccaoPessoa = s.direccaoPessoa
		}
}

//------------------------------------------------------------------------------------------------
//--------------------------------------- Cheques (em branco ou não) e Assert's -----
//------------------------------------------------------------------------------------------------
fact motor {
	all s : State, s' : s.next | estadoInicial[first] and estadosSeguintes[s] and estadosSeguintes[s'] and ((not (chamada[s,s']) and movimento[s,s']) || (ninguemMaisPodeSair[s] and ninguemMaisPodeEntrar[s] and chamada[s,s'] and not (movimento[s,s'])) || (ninguemMaisPodeSair[s] and ninguemMaisPodeEntrar[s] and garanteQueTodasAsPessoasSaoLevadas[s,s']))
}

assert condChamada {
	all p: Pessoa, s: State | s.localActualDePessoa[p] = Inicio
}

assert condSaemPessoas {	//num estado pessoa está dentro de uma carruagem e no estado seguinte pessoa está numa paragem
	no p: Pessoa | one s: State, s': s.next | p in s.localActualDePessoa.Carruagem and p in s'.localActualDePessoa.Fim
}

assert condEntramPessoas {	//num estado pessoa está numa paragem e no estado seguinte pessoa está dentro de uma carruagem
	no p: Pessoa | one s: State, s': s.next | p in s'.localActualDePessoa.Carruagem and p in s.localActualDePessoa.Paragem
}

assert condMovimentoCarruagens {
	no c: Carruagem | one s: State, s': s.next | one p1, p2: Paragem | p1 != p2 and s.localActualDeCarruagem[c] = p1 and s'.localActualDeCarruagem[c] = p2
}

assert condMovimentoCarruagemParaADireita {
	no c: Carruagem | one s: State, s': s.next | one p1, p2: Paragem | s.direccaoCarruagem[c] = Direita and p1.seguinte = p2 and s.localActualDeCarruagem[c] = p1 and s'.localActualDeCarruagem[c] = p2
}

assert condMovimentoCarruagemParaAEsquerda {
	no c: Carruagem | one s: State, s': s.next | one p1, p2: Paragem | s.direccaoCarruagem[c] = Esquerda and p1 = seguinte.p2 and s.localActualDeCarruagem[c] = p2 and s'.localActualDeCarruagem[c] = p1
}

assert condFinal {
	no s: last | (s.localActualDePessoa[Pessoa] = Fim)
}

//check condFinal for 2 but exactly 3 Pessoa, exactly 1 Carruagem, exactly 3 Paragem, 20 State //permite ver a situacao de pessoa ficar sem elevador atribuido
//check condFinal for 5 but exactly 5 Pessoa, exactly 2 Carruagem, exactly 5 Paragem, 20 State //para mais tempo
//run {} for 6	//caso base, em que uma pessoa com 2 paragens chama 1 elevador
//check condChamada for 5
//check condSaemPessoas for 5
//check condEntramPessoas for 5
//check condMovimentoCarruagens for 5
//check condMovimentoCarruagemParaAEsquerda for 6 but exactly 3 Paragem, exactly 2 Pessoa, 8 State	//permite ver entrada de uma pessoa e saida de outra
//check condMovimentoCarruagemParaAEsquerda for 6 but exactly 3 Paragem
//check condMovimentoCarruagemParaADireita for 6 but exactly 3 Paragem

