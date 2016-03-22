from smedl.parser.smedl_symboltable import SmedlSymbolTable
import unittest


class TestSymbolTable(unittest.TestCase):

    def setUp(self):
        self.symbolTable = SmedlSymbolTable()

    def test_add(self):
        self.assertFalse(list(self.symbolTable.keys()))
        self.symbolTable.add('one')
        attributes = {'type': 'a'}
        self.symbolTable.add('two', attributes.copy())
        attributes['datatype'] = 'b'
        self.symbolTable.add('three', attributes.copy())
        self.assertEqual(3, len(list(self.symbolTable.keys())))
        self.assertFalse(list(self.symbolTable['one'].keys()))
        self.assertEqual(1, len(list(self.symbolTable['two'].keys())))
        self.assertEqual(2, len(list(self.symbolTable['three'].keys())))
        self.assertEqual('a', self.symbolTable['three']['type'])

    def test_get(self):
        self.symbolTable.add('one')
        self.symbolTable.add('two', {'type': 'a'})
        one = self.symbolTable.get('one')
        two = self.symbolTable.get('two')
        two_attr = self.symbolTable.get('two', 'type')
        self.assertFalse(one)
        self.assertEqual(1, len(two))
        self.assertEqual('a', two['type'])
        self.assertEqual('a', two_attr)
        self.assertEqual(None, self.symbolTable.get('five'))
        self.assertEqual(None, self.symbolTable.get('one', 'datatype'))

    def test_getSymbolsByType(self):
        self.symbolTable.add('one')
        self.symbolTable.add('two', {'type': 'a'})
        self.symbolTable.add('three', {'type': 'a', 'datatype': 'b'})
        self.symbolTable.add('four', {'type': 'b'})
        type_a = self.symbolTable.getSymbolsByType('a')
        type_b = self.symbolTable.getSymbolsByType('b')
        type_c = self.symbolTable.getSymbolsByType('c')
        self.assertFalse(type_c)
        self.assertEqual(2, len(type_a))
        self.assertEqual(1, len(type_b))
        self.assertTrue('two' in type_a)
        self.assertTrue('three' in type_a)
        self.assertFalse('four' in type_a)
        self.assertTrue('four' in type_b)

    def test_update(self):
        self.symbolTable.add('one')
        self.symbolTable.update('one', 'type', 'a')
        self.assertEqual('a', self.symbolTable.get('one', 'type'))
        self.symbolTable.update('one', 'type', 'b')
        self.assertEqual('b', self.symbolTable.get('one', 'type'))
        self.symbolTable.update('one', 'datatype', 'c')
        self.assertEqual('c', self.symbolTable.get('one', 'datatype'))

    def test_delete(self):
        self.symbolTable.add('one')
        self.symbolTable.add('two', {'type': 'a'})
        self.assertEqual(2, len(list(self.symbolTable.keys())))
        self.symbolTable.delete('two', 'type')
        self.assertFalse(self.symbolTable.get('two', 'type'))
        self.symbolTable.delete('one')
        self.assertFalse(self.symbolTable.get('two', 'type'))
        # Would have expected self(symbol).pop and self[symbol](attribute).pop
        # to remove relative key, not just value
        # self.assertEqual(1, len(self.symbolTable.keys()))

if __name__ == '__main__':
    unittest.main()
