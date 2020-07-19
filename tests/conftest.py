import pytest

# Add command line options to set the RabbitMQ configuration
def pytest_addoption(parser):
    parser.addoption(
        '--rabbitmq-server', action='store', default='localhost',
        help='Name or address of the RabbitMQ server')
    parser.addoption(
        '--rabbitmq-port', action='store', type=int, default=5672,
        help='Port to connect to on the RabbitMQ server')
    parser.addoption(
        '--rabbitmq-user', action='store', default='guest',
        help='Username to use with the RabbitMQ server')
    parser.addoption(
        '--rabbitmq-pass', action='store', default='guest',
        help='Password to use with the RabbitMQ server')
    parser.addoption(
        '--rabbitmq-exchange', action='store',
        help='Exchange to use with the RabbitMQ server')
    parser.addoption(
        '--rabbitmq-vhost', action='store', default='/',
        help='Vhost to use with the RabbitMQ server')

@pytest.fixture(scope='session')
def rabbitmq_config(pytestconfig):
    result = dict()
    result['server'] = pytestconfig.getoption('rabbitmq_server')
    result['port'] = pytestconfig.getoption('rabbitmq_port')
    result['username'] = pytestconfig.getoption('rabbitmq_user')
    result['password'] = pytestconfig.getoption('rabbitmq_pass')
    result['exchange'] = pytestconfig.getoption('rabbitmq_exchange')
    result['vhost'] = pytestconfig.getoption('rabbitmq_vhost')
    return result
