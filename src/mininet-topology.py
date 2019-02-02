# -*- coding: utf-8 -*-

from mininet.topo import Topo

class MyTopo(Topo):
	def __init__(self):
		Topo.__init__(self)
		A = self.addSwitch('s1')
		aHost = self.addHost('h1')
		B = self.addSwitch('s2')
		bHost = self.addHost('h2')
		C = self.addSwitch('s3')
		cHost = self.addHost('h3')
		D = self.addSwitch('s4')
		dHost = self.addHost('h4')
		E = self.addSwitch('s5')
		eHost = self.addHost('h5')
		F = self.addSwitch('s6')
		fHost = self.addHost('h6')

		self.addLink(aHost, A, 0, 99)
		self.addLink(bHost, B, 0, 99)
		self.addLink(cHost, C, 0, 99)
		self.addLink(dHost, D, 0, 99)
		self.addLink(eHost, E, 0, 99)
		self.addLink(fHost, F, 0, 99)

    # example_topology:
		#      B ------> E
		#    / | \       ↑
		#   A  |  D <--- F
		#    \ | /
		#      C

		# Note: This network is more lenient than the diagram above in that
		# all links are bidirectional.

		self.addLink(A, B, 0, 0)
		self.addLink(A, C, 1, 0)
		self.addLink(B, C, 1, 1)
		self.addLink(B, D, 2, 0)
		self.addLink(B, E, 3, 1000)
		self.addLink(C, D, 2, 1)
		self.addLink(F, D, 0, 1000)
		self.addLink(F, E, 1, 1001)

topos = {'mytopo': lambda: MyTopo()}
