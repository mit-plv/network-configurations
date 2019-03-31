# -*- coding: utf-8 -*-

from mininet.topo import Topo

# Run on a mininet VM with:
# sudo mn --custom src/mininet-topology.py --topo mytopo --arp --mac --controller=remote,ip=<controller IP>,port=6633

class MyTopo(Topo):
	def __init__(self):
		Topo.__init__(self)
		sA = self.addSwitch('s1')
		hA = self.addHost('h1')
		sB = self.addSwitch('s2')
		hB = self.addHost('h2')
		sC = self.addSwitch('s3')
		hC = self.addHost('h3')
		sD = self.addSwitch('s4')
		hD = self.addHost('h4')
		sE = self.addSwitch('s5')
		hE = self.addHost('h5')
		sF = self.addSwitch('s6')
		hF = self.addHost('h6')

		#
		# example_topology:

		#    hB --- sB ----> sE      hE
		#          / | \   /          |
		# hA --- sA  |  sD ---- sF ---|
		#         \  | /   \      ↖______- hF
		#           sC - hC \__- hD

		# Note: This network is more lenient than the diagram above in that
		# all links are bidirectional. For easier debugging, directed edges
		# that are not present in the model topology have port number 1000.

		self.addLink(hA, sA, 1, 1)
		self.addLink(sA, sB, 2, 1)
		self.addLink(sA, sC, 3, 1)
		self.addLink(hB, sB, 1, 2)
		self.addLink(sB, sC, 3, 2)
		self.addLink(sB, sD, 4, 1)
		self.addLink(sB, sE, 5, 1000)
		self.addLink(hC, sC, 1, 3)
		self.addLink(sC, sD, 4, 2)
		self.addLink(hD, sD, 1, 3)
		self.addLink(sD, sE, 4, 1)
		self.addLink(sD, sF, 5, 1)
		self.addLink(hE, sF, 1, 2)
		self.addLink(hF, sF, 1, 1000)

topos = {'mytopo': lambda: MyTopo()}
